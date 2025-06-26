{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module Parser (module Parser) where

-- import Debug.Trace

import Text.Parsec
import ParsecToken (realNewLine)
import Unbound.Generics.LocallyNameless
import Control.Monad.Except
import Control.Monad hiding (ap)

import Data.Functor

import Syntax
import Lexer
import Helper (lam, forallty, cbind, var, tabs)
import BwdFwd
import Control.Monad.Identity (Identity(..))
import Data.Foldable (find)
import Prelude hiding (abs)
import Data.List (sortOn)


tryOrReturn :: a -> Parser a -> Parser a
tryOrReturn m p = try p <|> return m


type Parser a = ParsecT String (Context, [(Label, Int)], (String, Int)) (Except String) a
-- The states contain
--  1. context
--  2. list of constructor names
--  3. the current definition name (when parsing definitions) and its
--     argument number (if it is an ADT)

defaultDefName :: (String, Int)
defaultDefName = ("__NotInDefinitionMode", 0)

emptyParserCtx :: (Context, [(Label, Int)], (String, Int))
emptyParserCtx = (builtinCtx, builtinConsNames, defaultDefName)

updateCtx :: (Context -> Context) -> Parser ()
updateCtx f = modifyState $ \(x, y, z) -> (f x, y, z)

getCtx :: Parser Context
getCtx = getState <&> \(x, _, _) -> x

addConsName :: (Label, Int) -> Parser ()
addConsName l = modifyState $ \(x, y, z) -> (x, l:y, z)

getConsName :: Parser [Label]
getConsName = getState <&> \(_, y, _) -> map fst y

getConsNameArg :: Parser [(Label, Int)]
getConsNameArg = getState <&> \(_, y, _) -> y

updateDefName :: (String, Int) -> Parser ()
updateDefName name = modifyState $ \(x, y, _) -> (x, y, name)

getDefName :: Parser (String, Int)
getDefName = getState <&> \(_, _, z) -> z

runps :: Parser a -> String -> Either String (Either ParseError a)
runps p = runIdentity . runExceptT . runParserT p emptyParserCtx ""

runps' :: Parser a -> String -> a
runps' p s = case runIdentity . runExceptT . runParserT p emptyParserCtx "" $ s of
  Left e -> error $ show e
  Right (Left e) -> error $ show e
  Right (Right a) -> a

sourcePos :: Monad m => ParsecT s u m SourcePos
sourcePos = statePos <$> getParserState

sourceInfo :: Monad m => ParsecT s u m Info
sourceInfo =
      (\ st -> let pos = statePos st in Info (sourceName pos, sourceLine pos, sourceColumn pos))
  <$> getParserState

realNewLines :: Parser ()
realNewLines = void $ many realNewLine

----------------------------------------------------------------
-- * Program Parser

parseGlobal :: Parser Context
parseGlobal = whiteSpace >> realNewLines >> do
  many $ choice
    [ parseDataDef
    , parseEffDef
    , parseFunDef
    ] <* realNewLines
  getState <&> \(x, _, _) -> x

-- | effect name : a => b
parseEffDef :: Parser ()
parseEffDef = do
  info <- sourceInfo
  reserved "effect"
  name <- upperiden
  tyvarKinds <- many parseTVarWithKind
  reservedOp "="
  let parseOpDef = (do
        op <- loweriden
        colon
        a <- parseType
        reservedOp "=>"
        b <- parseType
        return (op, [a, b]))
  oplist <- sepBy1 parseOpDef (reservedOp "|")
  let effbody = foldr (\ (tyvar, k) res -> ADTBind k (bind (s2n tyvar) res))
                      (ADTCons oplist) tyvarKinds
  updateCtx (:< IDefEff info (name, effbody))

-- | data Name a b ... = cons1 A B ... | cons2 A B ... | ...
parseDataDef :: Parser ()
parseDataDef = do
  info <- sourceInfo
  reserved "data"
  name <- upperiden
  tyvarKinds <- many parseTVarWithKind
  reservedOp "="
  updateDefName (name, length tyvarKinds) -- now defining an ADT
  conslist <- sepBy1 parseDataDefCons (reservedOp "|")
  let adtbody = foldr (\ (tyvar, k) res -> ADTBind k (bind (s2n tyvar) res))
                      (ADTCons conslist) tyvarKinds
  updateDefName defaultDefName
  updateCtx (:< IDefADT info (name, bind (s2n name) adtbody))

parseTVarWithKind :: Parser (String, Kind)
parseTVarWithKind = choice
  [ try (brackets (loweriden <&> (, Pure)))
  , try (braces (loweriden <&> (, EffectKind)))
  , loweriden <&> (, Any)
  ]

-- | cons A B ..
-- We need to replace the recursive occurence of the current datatypes.
-- This is done in parseTVar.
parseDataDefCons :: Parser (Label, [Type])
parseDataDefCons = do
  cons <- loweriden
  tys <- many parseADTArg -- allow modal types without parentheses
  addConsName (cons, length tys)
  return (cons, tys)

-- | name : type
--   name pat1 pat2 = term
--   name pat3 pat4 = term
parseFunDef :: Parser ()
parseFunDef = do
  name <- loweriden
  updateDefName (name, -1) -- now defining a function
  colon
  (ty, tyvars) <- parseGlobalType
  realNewLines
  tm <- parseFunDefFrank name
    <|> (do
      casecls <- many (parseFunDefCase name tyvars <* realNewLines)
      case casecls of
        [] -> parseFunDefCase name tyvars >> throwError "empty case"
              -- throw a useful error message saying why parsing the function definition fails
        (hd:_) -> do
          let args = map (\n -> "arg" ++ show n) [1..(length $ fst hd)] -- arg-list
          return $ foldr lam (CasePat (map var args) casecls) args -- Construct the function term.
    )
  when (not (null tyvars) && not (isVal tm)) . throwError $
    "The function " ++ name ++ " violates value restriction."
  let tm' = foldr (uncurry tabs) tm tyvars -- Add term-level type abstractions.
  updateDefName defaultDefName
  updateCtx (:< TmVar (s2n name) ty (Just tm'))

parseFunDefCase :: String -> [(String, Kind)] -> Parser ([Pattern], CaseCls)
parseFunDefCase name tyvars = try $ do
  name' <- loweriden
  when (name /= name') . fail $ "Name " ++ name ++ " doesn't match " ++ name'
  try (do tyvars' <- many $ reservedOp "@" >> parseTVarWithKind
          when (tyvars' /= [] && tyvars /= tyvars') $ throwError "Type variable names mismatch")
  (pats, vars) <- parsePatterns
  reservedOp "="
  tm <- parseTerm
  return (pats, cbind vars tm)

-- | Special case of Frank-style thunk.
parseFunDefFrank :: String -> Parser Term
parseFunDefFrank name = try $ do
  name' <- loweriden
  when (name /= name') . fail $ "Name " ++ name ++ " doesn't match " ++ name'
  reservedOp "!"
  reservedOp "="
  tm <- parseTerm
  return $ lam "_" tm

----------------------------------------------------------------
-- * Pattern Parser

{-
  x
  ()
  n
  'c'
  "string"
  (P, Q)
  [P, Q, ...]
  single cons
  cons P Q ... (should be in parens unless for pairs and lists)
  parens (should try pair and unit first)
-}

-- | Parse a list of patterns. Return the list of all patterns and
-- variables inside from left to right.
parsePatterns:: Parser ([Pattern], [String])
parsePatterns = do
  patAndVars <- many parsePattern
  let pats = map fst patAndVars
  let vars = concatMap snd patAndVars
  return (pats, vars)

-- | At least one pattern. Deal with potential annotations. Used for lambdas.
parsePatterns1 :: Parser ([Pattern], [String], Maybe [Type])
parsePatterns1 = do
  patAndVarsAndAnnos <- many1 parsePatternAnno
  let pats = map (fst . fst) patAndVarsAndAnnos
  let vars = concatMap (snd . fst) patAndVarsAndAnnos
  let annos = mapM snd patAndVarsAndAnnos
  return (pats, vars, annos)

type PatternType = (Pattern, [String])

parsePatternAnno :: Parser (PatternType, Maybe Type)
parsePatternAnno = try ((,Nothing) <$> parsePattern)
  <|> parens ((,) <$> (parsePatternWithCons <* colon) <*> (Just <$> parseType))

-- | Return the pattern and variable inside it from left to right
parsePattern :: Parser PatternType
parsePattern = choice
  [ patternUnit
  , patternVar
  , patternChar
  , patternString
  , patternList
  , patternInt
  , patternSingleCons
  , patternPair
  , parens parsePatternWithCons
  ]

parsePatternWithCons :: Parser PatternType
parsePatternWithCons = choice
  [ patternUnit
  , patternVar
  , patternChar
  , patternString
  , patternList
  , patternInt
  , patternSingleCons
  , patternPair
  , patternCons -- only difference
  , parens parsePatternWithCons
  ]

-- | Suppose the name is a defined constructor name. Check the arg numbers.
checkConsArgNum :: Label -> Int -> Parser ()
checkConsArgNum cons num = do
  num' <- getConsArgNum cons
  if num == num' then return ()
  else throwError $ cons ++ " expects " ++ show num' ++ " args but given " ++ show num

getConsArgNum :: Label -> Parser Int
getConsArgNum cons = do
  consNameArgs <- getConsNameArg
  case find ((cons ==) . fst) consNameArgs of
    Nothing -> throwError $ cons ++ " is not a constructor"
    Just (_, num) -> return num

isCons :: Label -> Parser ()
isCons cons = do
  consNames <- getConsName
  case find (cons ==) consNames of
    Nothing -> fail $ cons ++ " is not a constructor"
    Just _  -> return ()

notCons :: Label -> Parser ()
notCons cons = do
  consNames <- getConsName
  case find (cons ==) consNames of
    Nothing -> return ()
    Just _  -> fail $ cons ++ " is a constructor"

-- I don't think I need to check the number of cons args.
-- If not enough or more args are given, it will be caught in the type checker.
patternSingleCons :: Parser PatternType
patternSingleCons = try $ do
  cons <- loweriden
  isCons cons
  num <- getConsArgNum cons
  when (num /= 0) $ fail "not a single constructor"
    -- Ideally I should `throwError` instead of `fail`. But that doesn't work. I don't know why.
  return (PCons cons [], [])

patternCons :: Parser PatternType
patternCons = try $ do
  cons <- loweriden
  isCons cons
  pats <- many parsePattern
  checkConsArgNum cons (length pats)
  return (PCons cons (map fst pats), concatMap snd pats)

patternPair :: Parser PatternType
patternPair = try . parens $ do
  p1 <- parsePatternWithCons
  comma
  p2 <- parsePatternWithCons
  return (PCons "pair" [fst p1, fst p2], snd p1 ++ snd p2)

patternList :: Parser PatternType
patternList = brackets $ do
  list <- sepBy parsePatternWithCons comma
  return $ foldr (\ (pat, names) (pat', names') ->
                    (PCons "cons" [pat, pat'], names ++ names'))
                  (PCons "nil" [], []) list

patternString :: Parser PatternType
patternString = stringLiteral >>= \ s ->
  return (foldr (\ x t -> PCons "cons" [PChar x, t]) (PCons "nils" []) s, [])

patternInt :: Parser PatternType
patternInt = natural >>= \ n -> return (PInt $ fromIntegral n, [])
-- patternInt = try $ natural >>= \ n -> return (PInt $ fromIntegral n, [])
  -- We need to try because it includes minus numbers, and -> also starts with a minus.

patternChar :: Parser PatternType
patternChar = charLiteral >>= \ c -> return (PChar c, [])

patternUnit :: Parser PatternType
patternUnit = reservedOp "()" $> (PCons "unit" [], [])

patternVar :: Parser PatternType
patternVar = try $ do
  name <- loweriden
  notCons name
  return (PVar, [name])

----------------------------------------------------------------
-- * Term Parser

{-
  Base terms
  List, String, Pair, single cons
  App and TApp (left recursive, left associative), Cons, Do, Mask
  Expr (left recursive)
  Anno
  Handle, Let, Case, Seq (left recursive, right associative)
  lambda
-}

-- There is something wrong with parseAnno which makes the parser non-terminating.
-- I don't know why. I will just restrict the syntax of annotation to atom : type.

parseBaseTerm :: Parser Term
parseBaseTerm = choice
  [ parseUnit
  , parseInt
  , parseChar
  , parseString
  ]

-- | n ∈ ℕ
parseInt :: Parser Term
parseInt = do
  info <- sourceInfo
  n <- natural
  return . ITmInt info $ fromIntegral n

parseChar :: Parser Term
parseChar = do
  info <- sourceInfo
  c <- charLiteral
  return $ ITmChar info c

parseString :: Parser Term
parseString = do
  info <- sourceInfo
  s <- stringLiteral
  return $ foldr (\ x t -> ICons info "cons" [TmChar x, t]) (ICons info "nils" []) s
  -- all use the starting position

parseUnit :: Parser Term
parseUnit = do
  info <- sourceInfo
  reservedOp "()"
  return $ ICons info "unit" []

parseAtom :: Parser Term
parseAtom = choice
  [ parseBaseTerm
  , parseSingleCons
  , parseVar
  , parseList
  , parseThunk
  , parsePair
  , parens parseTerm
  ]

termParsers :: [Parser Term]
termParsers =
  [ parseLamAll
  , parseLet
  , parseLetRec
  , parseIf
  , parseSeq
  ]
  -- ++ seqArgParsers

seqArgParsers :: [Parser Term]
seqArgParsers =
  [ parseHandle
  , parseCaseSplit
  , parseCons
  , parsePrint
  , parseAnno
  ]
  -- ++ exprArgParsers

annoArgParsers :: [Parser Term]
annoArgParsers = [ parseExpr ]

exprArgParsers :: [Parser Term]
exprArgParsers = [ parseApp ]
  -- ++ appArgParsers

appArgParsers :: [Parser Term]
appArgParsers =
  -- No constructor because it never gives a function.
  [ parseFst
  , parseSnd
  , parseDo   -- shouldn't be here if we'd like to omit unit arguments of do
              -- It's fine I think. Just guarantee that no omission is
              -- allowed when we want to immediately apply the result of Do afterwards
  , parseMask
  , parseForce
  -- , parseAtom -- included by parseForce
  ]

parseTerm :: Parser Term
parseTerm = choice termParsers

-- | x A B ...
parseVar :: Parser Term
parseVar = do
  info <- sourceInfo
  name <- loweriden
  return $ IVar info (s2n name)

parseAnno :: Parser Term
parseAnno = do
  info <- sourceInfo
  m <- choice annoArgParsers
  tryOrReturn m $ do
    colon
    a <- parseType
    return $ IAnno info m a

-- -- | fun x -> m
-- parseLam :: Parser Term
-- parseLam = do
--   info <- sourceInfo
--   reserved "fun"
--   (pats, vars) <- parsePatterns
--   arrow
--   m <- parseTerm
--   return $ ILamCase info (pats, cbind vars m)

parseLamAll :: Parser Term
parseLamAll = do
  info <- sourceInfo
  reserved "fun"
  bindings <- many1 (parseLamTAbs <|> parseLamPat <|> fail "not a lambda")
  arrow
  body <- parseTerm
  let fun = foldr ($) body bindings
  return $ case fun of
    ITAbs _ knd bnd -> ITAbs info knd bnd
    ILamCase _ tm -> ILamCase info tm
    ILamCaseAnno _ tys tm -> ILamCaseAnno info tys tm
    _ -> error "impossible"

parseLamTAbs :: Parser (Term -> Term)
parseLamTAbs = do
  info <- sourceInfo
  reservedOp "@"
  -- alpha <- loweriden
  (alpha, knd) <- parseTVarWithKind
  return $ \t -> ITAbs info knd (bind (s2n alpha) t)

parseLamPat :: Parser (Term -> Term)
parseLamPat = do
  info <- sourceInfo
  (pats, vars, tyannos) <- parsePatterns1
  case tyannos of
    Nothing  -> return $ \t -> ILamCase info (pats, cbind vars t)
    Just tys -> return $ \t -> ILamCaseAnno info tys (pats, cbind vars t)

-- | fun x : A -> m
-- parseLamAnno :: Parser Term
-- parseLamAnno = do
--   reserved "fun"
--   x <- identifier
--   colon
--   a <- parseType
--   arrow
--   m <- parseTerm
--   return $ lamA x a m

-- | Frank-style thunks: {M}
parseThunk :: Parser Term
parseThunk = do
  info <- sourceInfo
  m <- braces parseTerm
  return $ ILam info (bind (s2n "_") m)

-- | Frank-style force: M!
parseForce :: Parser Term
parseForce = do
  info <- sourceInfo
  m <- parseAtom
  tryOrReturn m $ do
    reservedOp "!"
    return $ IApp info m tmUnit

-- | (M, N)
parsePair :: Parser Term
parsePair = try . parens $ do
  info <- sourceInfo
  m <- parseTerm
  comma
  n <- parseTerm
  return $ ICons info "pair" [m, n]

-- | [M1, M2, ...]
parseList :: Parser Term
parseList = do
  info <- sourceInfo
  brackets $ (do
      m <- parseTerm
      ms <- many $ comma >> parseTerm
      return $ foldr (\ x t -> ICons info "cons" [x, t]) (ICons info "nil" []) (m:ms)
      -- NOTE: for simplicity, only using the starting position here
    ) <|> return (ICons info "nil" [])

parseFst :: Parser Term
parseFst = do
  info <- sourceInfo
  reserved "fst"
  m <- parseAtom
  return $ ICasePat info [m] [([PCons "pair" [PVar, PVar]], cbind ["x", "y"] (var "x"))]

parseSnd :: Parser Term
parseSnd = do
  info <- sourceInfo
  reserved "snd"
  m <- parseAtom
  return $ ICasePat info [m] [([PCons "pair" [PVar, PVar]], cbind ["x", "y"] (var "y"))]

parsePrint :: Parser Term
parsePrint = do
  info <- sourceInfo
  reserved "print"
  s <- stringLiteral
  return $ IPrint info s

-- | H
parseHandler :: Parser HandlerClauses
parseHandler = do
  info <- sourceInfo
  clauses <- braces $ sepBy (parseRetCls <|> parseOpCls) comma
  let retNum = length $ filter (("return" ==) . fst) clauses
  when (retNum > 1) $ throwError "There should be at most one return clause."
  let dummyRetCls = ("return", ([PVar], cbind ["x"] (IVar info (s2n "x"))))
  let newClauses = if retNum == 0 then dummyRetCls:clauses else clauses
  let sortedClauses = sortOn (\ s -> fst s == "return") newClauses
  -- make sure that return clause is the last one
  return sortedClauses


parseRetCls :: Parser HandlerClause
parseRetCls = do
  reserved "return"
  (pats, vars) <- parsePatterns
  when (length pats /= 1) $ throwError "Return clause should have one argument."
  reservedOp "=>"
  m <- parseTerm
  return ("return", (pats, cbind vars m))

parseOpCls :: Parser HandlerClause
parseOpCls = do
  opname <- loweriden
  (pats, vars) <- parsePatterns
  when (length pats /= 2) $ throwError "Operation clause should have two arguments."
  reservedOp "=>"
  m <- parseTerm
  return (opname, (pats, cbind vars m))

-- | M N1 @A1 @A2 N2 ...
parseApp :: Parser Term
parseApp = do
  info <- sourceInfo
  m <- choice appArgParsers
  tryOrReturn m $ do
    ns <- many1 ((reservedOp "@" >> parseModArg <&> Left) <|> (parseAtom <&> Right))
    return $ foldl (\ res cur -> case cur of
                                  Left ty -> ITApp info res ty
                                  Right tm -> IApp info res tm) m ns

-- | cons M N
parseCons :: Parser Term
parseCons = try $ do
  info <- sourceInfo
  cons <- loweriden
  isCons cons
  args <- many parseAtom
  return $ ICons info cons args

-- | cons
parseSingleCons :: Parser Term
parseSingleCons = try $ do
  info <- sourceInfo
  cons <- loweriden
  isCons cons
  num <- getConsArgNum cons
  when (num /= 0) $ fail "not a single constructor"
  return $ ICons info cons []

parsePlusMinus :: Parser Term
parsePlusMinus = do
  info <- sourceInfo
  m <- choice exprArgParsers
  tryOrReturn m $ do
    opr <- (reservedOp "+" $> "+") <|> (reservedOp "-" $> "-")
    n <- choice $ parsePlusMinus : exprArgParsers
    return $ IExpr info opr m n

parseRelation :: Parser Term
parseRelation = do
  info <- sourceInfo
  m <- choice $ parsePlusMinus : exprArgParsers
  tryOrReturn m $ do
    opr <-  (reservedOp "==" $> "==")
        <|> (reservedOp "/=" $> "/=")
        <|> (reservedOp "<=" $> "<=")
        <|> (reservedOp ">=" $> ">=")
        <|> (reservedOp "<" $> "<")
        <|> (reservedOp ">" $> ">")
    n <- choice $ parsePlusMinus : exprArgParsers
    return $ IExpr info opr m n

parseExpr :: Parser Term
parseExpr = parseRelation

-- | handle M with H
parseHandle :: Parser Term
parseHandle = do
  info <- sourceInfo
  reserved "handle"
  anno <- try (angles parseEffect <&> Just) <|> return Nothing
  m <- parseTerm
  reserved "with"
  h <- parseHandler
  return $ IHandle info anno m h

-- | M; N
parseSeq :: Parser Term
parseSeq = do
  info <- sourceInfo
  m <- choice seqArgParsers
  tryOrReturn m $ do
    semi
    n <- parseTerm
    return $ ILet info m (bind (s2n "_") n)

-- | let x = M in N
parseLet :: Parser Term
parseLet = do
  info <- sourceInfo
  reserved "let"
  x <- identifier
  reservedOp "="
  m <- parseTerm
  reserved "in"
  n <- parseTerm
  return $ ILet info m (bind (s2n x) n)

-- | letrec x : A = M in N
parseLetRec :: Parser Term
parseLetRec = do
  info <- sourceInfo
  reserved "letrec"
  x <- identifier
  colon
  a <- parseType
  reservedOp "="
  m <- parseTerm
  reserved "in"
  n <- parseTerm
  return $ ILetRec info a $ bind (s2n x) (m, n)

-- | do l M
parseDo :: Parser Term
parseDo = do
  info <- sourceInfo
  reserved "do"
  l <- identifier
  try (do m <- parseAtom
          return $ IDo info l m) <|> return (IDo info l (Cons "unit" []))

-- | mask<L> M
parseMask :: Parser Term
parseMask = do
  info <- sourceInfo
  reserved "mask"
  e <- angles parseEffect
  m <- parseAtom
  return $ IMask info e m

-- | if M then N1 else N2
parseIf :: Parser Term
parseIf = do
  info <- sourceInfo
  reserved "if"
  m <- parseTerm
  whiteSpace
  reserved "then"
  n1 <- parseTerm
  whiteSpace
  reserved "else"
  n2 <- parseTerm
  return $ IIf info m n1 n2

parseCaseSplit :: Parser Term
parseCaseSplit = do
  info <- sourceInfo
  reserved "case"
  ms <- many parseAtom -- function application must be in parentheses
  reserved "of"
  braces $ do
    cls <- parseCaseCls
    clss <- many (comma >> parseCaseCls)
    return $ ICasePat info ms (cls:clss)

parseCaseCls :: Parser ([Pattern], CaseCls)
parseCaseCls = do
  (pats, vars) <- parsePatterns
  reservedOp "->"
  m <- parseTerm
  return (pats, cbind vars m)


----------------------------------------------------------------
-- * Type Parser

-- Precedence levels:
--  Base, single ADT without arguments
--  Mod  (take arguments, right associative)
--  ADT  (take arguments, left associative)
--  *, + (left recursive)
--  ->   (left recursive)
--  forall

-- | Basetypes
parseBaseType :: Parser Type
parseBaseType = choice
  [ parseIntType
  , parseUnitType
  , parseCharType
  , parseStringType
  , parseTVar
  ]

-- | a
parseTVar :: Parser Type
parseTVar = try $ do
  info <- sourceInfo
  name <- loweriden
  return $ ITVar info (s2n name)

-- | 1
parseUnitType :: Parser Type
parseUnitType = do
  info <- sourceInfo
  char '1'
  whiteSpace
  return $ IADT info "Unit" []

-- | Int
parseIntType :: Parser Type
parseIntType = do
  info <- sourceInfo
  reserved "Int"
  return $ ITInt info

-- | Char
parseCharType :: Parser Type
parseCharType = do
  info <- sourceInfo
  reserved "Char"
  return $ ITChar info

-- | String
parseStringType :: Parser Type
parseStringType = do
  info <- sourceInfo
  reserved "String"
  return $ IADT info "List" [TChar]

-- | Frank-style thunk type: {A}
parseThunkType :: Parser Type
parseThunkType = do
  info <- sourceInfo
  ty <- braces parseType
  return $ IArr info (ityUnit info) ty

-- | DataName
parseSingleADT :: Parser Type
parseSingleADT = try $ do
  info <- sourceInfo
  name <- upperiden
  (name', argnum') <- getDefName
  if name == name' then do -- defining ADT
    when (argnum' /= 0) $ fail "Not a single ADT without arguments"
    return $ ITVar info (s2n name)
  else do -- using ADT
    ctx <- getCtx
    argnum <- argNumADT ctx name
    when (argnum /= 0) $ fail "Not a single ADT without arguments"
    return $ IADT info name []

-- | μA
parseModalType :: Parser Type
parseModalType = do
  info <- sourceInfo
  mu <- parseModal
  a <- parseModArg
  return $ IMod info mu a

parseModArg :: Parser Type
parseModArg = choice
  [ parseBaseType
  , parseSingleADT
  , parseModalType
  , parseThunkType
  , parens parseType
  ]

-- | [E] or <L | D> or <D>
parseModal :: Parser Type
parseModal = do
  info <- sourceInfo
  choice
    [ brackets (parseEffect <&> IAbs info)
    , angles (do
          l <- parseEffect
          try (do whiteSpace >> char '|' >> whiteSpace
                  r <- parseEffect
                  return $ IRel info l r)
            <|> return (IRel info En l)
          )
    ]

parseLabel :: Parser String
parseLabel = alphaiden

parseEffect :: Parser Effect
parseEffect = do
  effectlist <- sepBy parseEff comma
  return $ foldr Ec En effectlist

parseEff :: Parser Eff
parseEff = do
  name <- upperiden -- effect name are uppercase
  tys <- many parseEffArg
  return $ Eff name tys

-- | DataName A B ...
parseADT :: Parser Type
parseADT = do
  info <- sourceInfo
  name <- upperiden
  tys <- many parseADTArg
  (name', argnum') <- getDefName
  if name == name' then do -- defining ADT
    when (argnum' /= length tys) $ throwError "parseADT: arg number mismatch"
    return $ ITVar info (s2n name)
  else do -- using ADT
    ctx <- getCtx
    argnum <- argNumADT ctx name
    when (argnum /= length tys) $ throwError "parseADT: arg number mismatch"
    return $ IADT info name tys

parseADTArg :: Parser Type
parseADTArg = parseModArg

parseEffArg :: Parser Type
parseEffArg = parseModArg

-- | A * B
parseProduct :: Parser Type
parseProduct = do
  info <- sourceInfo
  a <- parseProdArg
  tryOrReturn a $ do
    reservedOp "*"
    b <- parseProdArg
    return $ ityPair info a b

parseProdArg :: Parser Type
parseProdArg = choice
  [ parseBaseType
  , parseSingleADT
  , parseModalType
  , parseThunkType
  , parseADT
  , parens parseType
  ]

-- | A -> B
parseArrow :: Parser Type
parseArrow = try $ do
  info <- sourceInfo
  a <- parseArrowArg
  tryOrReturn a $ do
    arrow
    b <- parseType
    return $ IArr info a b

parseArrowArg :: Parser Type
parseArrowArg = choice
  [ parseProduct ]

parseType :: Parser Type
parseType = choice
  [ parseArrow
  , parseForall
  ]

-- | forall a b c ... . A
parseForall :: Parser Type
parseForall = fst <$> parseGlobalForall

parseGlobalForall :: Parser (Type, [(String, Kind)])
parseGlobalForall = do
  reserved "forall"
  binds <- many parseTVarWithKind
  dot
  a <- parseType
  return (foldr (uncurry forallty) a binds, binds)

-- | Return a type and a list of type variables with their kinds (if it is a forall type)
parseGlobalType :: Parser (Type, [(String, Kind)])
parseGlobalType =  parseGlobalForall
               <|> (, []) <$> parseType
