{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, ScopedTypeVariables, GeneralizedNewtypeDeriving, StandaloneDeriving, DeriveGeneric, InstanceSigs,
PatternSynonyms #-}

module Syntax (module Syntax) where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Except

import Unbound.Generics.LocallyNameless
import BwdFwd hiding ((<><))
import GHC.Generics (Generic)
import Data.List (sortOn)

type Label = String
type ADTName = String
type EffectName = String

type SourceInfo = (String, Int, Int) -- (File, Line, Column)
data Info = Info SourceInfo | None
  deriving (Show, Generic, Eq)
instance Alpha Info
instance Subst Type Info
instance Subst Term Info

data Kind
  = Pure
  | Any
  | EffectKind
  deriving (Generic, Eq, Show)
  -- Pure <= Any

instance Alpha Kind
instance Subst Type Kind where

instance Ord Kind where
  (<=) :: Kind -> Kind -> Bool
  Pure <= Any = True
  k <= k'     = k == k'

class Meetable a where
  meet :: a -> a -> a

instance Meetable Kind where
  Pure `meet` _  = Pure
  _ `meet` Pure  = Pure
  Any `meet` Any = Any
  _ `meet` _     = error "Effect kind does not support meet."

data Type
  = ITVar Info (Name Type)   -- type var
  | IArr Info Type Type
  | IAll Info Kind (Bind (Name Type) Type)
  | IMod Info Type Type      -- modal types
  -- modalities
  | IAbs Info Effect         -- absolute modality
  | IRel Info Effect Effect  -- relative modality
  -- algebraic datatypes
  | IADT Info ADTName [Type]
  -- other primitive base types
  | ITInt Info
  | ITChar Info
  deriving (Generic, Show)
-- Define types and effects together to reuse var definitions.

pattern TVar :: Name Type -> Type
pattern TVar name <- ITVar _ name where
  TVar name = ITVar None name
pattern Arr :: Type -> Type -> Type
pattern Arr t1 t2 <- IArr _ t1 t2 where
  Arr t1 t2 = IArr None t1 t2
pattern All :: Kind -> Bind (Name Type) Type -> Type
pattern All k b <- IAll _ k b where
  All k b = IAll None k b
pattern Mod :: Type -> Type -> Type
pattern Mod t1 t2 <- IMod _ t1 t2 where
  Mod t1 t2 = IMod None t1 t2
pattern Abs :: Effect -> Type
pattern Abs e <- IAbs _ e where
  Abs e = IAbs None e
pattern Rel :: Effect -> Effect -> Type
pattern Rel e1 e2 <- IRel _ e1 e2 where
  Rel e1 e2 = IRel None e1 e2
pattern ADT :: ADTName -> [Type] -> Type
pattern ADT name ts <- IADT _ name ts where
  ADT name ts = IADT None name ts
pattern TInt :: Type
pattern TInt <- ITInt _ where
  TInt = ITInt None
pattern TChar :: Type
pattern TChar <- ITChar _ where
  TChar = ITChar None

eraseInfo :: Type -> Type
eraseInfo (ITVar _ x) = TVar x
eraseInfo (IArr _ a b) = Arr (eraseInfo a) (eraseInfo b)
eraseInfo (IAll _ k bnd) = All k bnd'
  where bnd' = runFreshM $ do
          (alpha, body) <- unbind bnd
          return $ bind alpha (eraseInfo body)
eraseInfo (IMod _ mu nu) = Mod (eraseInfo mu) (eraseInfo nu)
eraseInfo (IAbs _ e) = Abs (sortEffect e)
eraseInfo (IRel _ l d) = Rel (sortEffect l) (sortEffect d)
eraseInfo (IADT _ name ts) = ADT name (map eraseInfo ts)
eraseInfo ITInt{} = TInt
eraseInfo ITChar{} = TChar

sortEffect :: Effect -> Effect
sortEffect = row2eff . sortOn effName . eff2row

data ADTBody = ADTCons [(Label, [Type])]
             | ADTBind Kind (Bind (Name Type) ADTBody)
  deriving (Generic, Show)

instance Alpha ADTBody
instance Subst Type ADTBody

type ADTType = (ADTName, Bind (Name Type) ADTBody)
type EffectType = (EffectName, ADTBody) -- no recursive effects
  -- each constructor in ADTCons has form `(op, [a, b])`

instance Eq Type where
  a == b = aeq (eraseInfo a) (eraseInfo b)
  -- NOTE: order of effects should not matter
  -- Currently resolve this problem by sorting effects before comparison


infixr 5 `Arr`

instance Alpha Type
instance Subst Type Type where
  isvar (TVar alpha) = Just (SubstName alpha)
  isvar _            = Nothing

data Eff = Eff { effName :: EffectName, effArgs :: [Type] }
  deriving (Generic, Show)
-- The length of effArgs should match the number of arguments in effect definitions.
-- The only exception is for masking where effArgs are always empty.

data Effect
  = En
  | Eff `Ec` Effect
  deriving (Generic, Show)

instance Alpha Eff
instance Alpha Effect where
  aeq' _ e1 e2 = e1 == e2
instance Subst Type Eff
instance Subst Type Effect

instance Eq Effect where
  (==) :: Effect -> Effect -> Bool
  e == f = e ==: f


-- * Effects


infix 5 +:
infix 5 -:
infix 5 \/
infix 5 /\
infix 5 ><:
infix 4 <:
infix 4 ==:
infix 7 |>

class Rowable a where
  (+:) :: a -> a -> a
  (-:) :: a -> a -> a
  (<:) :: a -> a -> Bool
  (==:) :: a -> a -> Bool
  x ==: y = x <: y && y <: x
  (\/) :: a -> a -> Maybe a
  (/\) :: a -> a -> Maybe a
  (><:) :: a -> a -> (a, a)
  x ><: y = (x -: y, y -: x)

type Row = [Eff]

instance Rowable Row where
  (+:) :: Row -> Row -> Row
  (+:) = (++)

  (-:) :: Row -> Row -> Row
  r1 -: []     = r1
  r1 -: (l:r2) = case findEffName (effName l) r1 of -- (-:) only looks at labels
    Nothing  -> r1  -: r2
    Just r1' -> r1' -: r2

  (<:) :: Row -> Row -> Bool
  []     <: _  = True
  (l:r1) <: r2 = case findEffect l r2 of
    Left _  -> False
    Right r2' -> r1 <: r2'

  (\/) :: Row -> Row -> Maybe Row
  r  \/ [] = Just r
  [] \/ r  = Just r
  (l1:r1) \/ r2 = case findEffect l1 r2 of
    Left False -> Nothing
    Left True  -> (l1 :) <$> (r1 \/ r2)
    Right r2'  -> (l1 :) <$> (r1 \/ r2')

  (/\) :: Row -> Row -> Maybe Row
  _  /\ [] = Just []
  [] /\ _  = Just []
  (l1:r1) /\ r2 = case findEffect l1 r2 of
    Left False -> Nothing
    Left True  -> r1 /\ r2
    Right r2'  -> (l1 :) <$> (r1 /\ r2')

-- | Find an effect name from the left and return the remaining row if succeed.
findEffName :: Label -> Row -> Maybe Row
findEffName _ [] = Nothing
findEffName l (e:r) =
  if l == effName e then return r
  else findEffName l r >>= \r' -> return (e:r')

-- | Find an effect from the left and return the remaining row if succeed.
-- Left True : does not exist
-- Left False : type args do not match
findEffect :: Eff -> Row -> Either Bool Row
findEffect _ [] = Left True
findEffect l (e:r) =
  if effName l == effName e then
    if effArgs l == effArgs e then Right r
    else Left False
  else findEffect l r >>= \r' -> Right (e:r')

-- | Transform an effect type to a row of labels.
eff2row :: Effect -> Row
eff2row En         = []
eff2row (l `Ec` e) = l : eff2row e

-- | Transform a row type to an effect type.
row2eff :: Row -> Effect
row2eff = foldr Ec En

countEff :: Label -> Effect -> Int
countEff l e = length . filter ((==l) . effName) $ eff2row e

instance Rowable Effect where
  (+:) :: Effect -> Effect -> Effect
  e +: f = row2eff (eff2row e +: eff2row f)
  (-:) :: Effect -> Effect -> Effect
  e -: f = row2eff (eff2row e -: eff2row f)
  (<:) :: Effect -> Effect -> Bool
  e <: f = eff2row e <: eff2row f
  (\/) :: Effect -> Effect -> Maybe Effect
  e \/ f = eff2row e \/ eff2row f >>= Just. row2eff
  (/\) :: Effect -> Effect -> Maybe Effect
  e /\ f = eff2row e /\ eff2row f >>= Just. row2eff


-- * Modalities

-- Identity modality
one :: Type
one = Rel En En

instance Semigroup Type where
  _         <> Abs e      =  Abs e
  Abs e     <> Rel l d    =  Abs (d +: (e -: l))
  -- Rel l1 d1 <> Rel l2 d2 = Rel (l1 +: (l2 -: d1)) (d2 +: (d1 -: l2))
  Rel l1 d1 <> Rel l2 d2  =  Rel (l1 +: l) (d2 +: d) where (l, d) = l2 ><: d1
  _         <> _          =  error "Internal error: Not a modality."

(|>) :: Type -> Effect -> Effect
Abs e   |> _  =  e
Rel l d |> e  =  d +: (e -: l)
_       |> _  =  error "Internal error: Not a modality."

instance Monoid Type where
  mempty  = one
  mappend = (<>)


-- `ModTrans mu nu e` holds if `mu => nu @ e`
modTrans :: Type -> Type -> Effect -> Bool
modTrans (Abs e) mu f = e <: (mu |> f)
modTrans (Rel l1 d1) (Rel l2 d2) e =
  let (l, d) = l1 ><: d1
  in let (l', d') = l2 ><: d2
  in (l, d) == (l', d') && l1 <: e && l2 <: e
modTrans _ _ _ = False

-- * Terms

data Term
  = IVar Info (Name Term)
  | ILam Info (Bind (Name Term) Term)
  | ILamCase Info CasePatClause -- only allow one case clause
  | ILamCaseAnno Info [Type] CasePatClause
  | IAnno Info Term Type
  | IApp Info Term Term
  | ITApp Info Term Type
  | ILet Info Term (Bind (Name Term) Term)
  | ILetRec Info Type (Bind (Name Term) (Term, Term))
  | IDo Info Label Term
  | IMask Info Effect Term
  | IHandle Info (Maybe Effect) Term HandlerClauses
  | ITAbs Info Kind (Bind (Name Type) Term)
  -- adt
  | ICons Info Label [Term]
  | ICasePat Info [Term] CasePatClauses
  -- other constructs
  | ITmInt Info Int
  | ITmChar Info Char
  | IExpr Info String Term Term
  | IIf Info Term Term Term
  | IPrint Info String
  -- merely for semantics
  | Fix (Bind (Name Term) Term)
  | Dor (Label, Int) Term (Bind (Name Term) Term)
  deriving (Generic, Show)

pattern Var :: Name Term -> Term
pattern Var x <- IVar _ x where
  Var x = IVar None x
pattern Lam :: Bind (Name Term) Term -> Term
pattern Lam b <- ILam _ b where
  Lam b = ILam None b
pattern LamCase :: CasePatClause -> Term
pattern LamCase b <- ILamCase _ b where
  LamCase b = ILamCase None b
pattern LamCaseAnno :: [Type] -> CasePatClause -> Term
pattern LamCaseAnno ts b <- ILamCaseAnno _ ts b where
  LamCaseAnno ts b = ILamCaseAnno None ts b
pattern Anno :: Term -> Type -> Term
pattern Anno m t <- IAnno _ m t where
  Anno m t = IAnno None m t
pattern App :: Term -> Term -> Term
pattern App m n <- IApp _ m n where
  App m n = IApp None m n
pattern TApp :: Term -> Type -> Term
pattern TApp m t <- ITApp _ m t where
  TApp m t = ITApp None m t
pattern Let :: Term -> Bind (Name Term) Term -> Term
pattern Let m b <- ILet _ m b where
  Let m b = ILet None m b
pattern LetRec :: Type -> Bind (Name Term) (Term, Term) -> Term
pattern LetRec t b <- ILetRec _ t b where
  LetRec t b = ILetRec None t b
pattern Do :: Label -> Term -> Term
pattern Do l m <- IDo _ l m where
  Do l m = IDo None l m
pattern Mask :: Effect -> Term -> Term
pattern Mask e m <- IMask _ e m where
  Mask e m = IMask None e m
pattern Handle :: Maybe Effect -> Term -> HandlerClauses -> Term
pattern Handle e m h <- IHandle _ e m h where
  Handle e m h = IHandle None e m h
pattern TAbs :: Kind -> Bind (Name Type) Term -> Term
pattern TAbs k b <- ITAbs _ k b where
  TAbs k b = ITAbs None k b
pattern Cons :: Label -> [Term] -> Term
pattern Cons l ms <- ICons _ l ms where
  Cons l ms = ICons None l ms
pattern CasePat :: [Term] -> CasePatClauses -> Term
pattern CasePat ms cs <- ICasePat _ ms cs where
  CasePat ms cs = ICasePat None ms cs
pattern TmInt :: Int -> Term
pattern TmInt n <- ITmInt _ n where
  TmInt n = ITmInt None n
pattern TmChar :: Char -> Term
pattern TmChar c <- ITmChar _ c where
  TmChar c = ITmChar None c
pattern Expr :: String -> Term -> Term -> Term
pattern Expr s m n <- IExpr _ s m n where
  Expr s m n = IExpr None s m n
pattern If :: Term -> Term -> Term -> Term
pattern If m n o <- IIf _ m n o where
  If m n o = IIf None m n o
pattern Print :: String -> Term
pattern Print s <- IPrint _ s where
  Print s = IPrint None s

type CasePatClause  = ([Pattern], CaseCls)
type CasePatClauses = [CasePatClause]
type HandlerClause  = (Label, CasePatClause)
type HandlerClauses = [HandlerClause]

data Pattern = PVar | PCons Label [Pattern] | PChar Char | PInt Int
  deriving (Generic, Show)

-- a casecls binds all variables in its patterns from left to right
data CaseCls = CaseTerm Term
             | CaseBind (Bind (Name Term) CaseCls)
  deriving (Generic, Show)

argNum :: CasePatClause -> Contextual Int
argNum (pats, _) = return $ length pats

instance Eq Term where
    (==) = aeq

instance Alpha Term
instance Subst Type Term
instance Alpha CaseCls
instance Subst Type CaseCls
instance Alpha Pattern
instance Subst Type Pattern

instance Subst Term Kind
instance Subst Term Type
instance Subst Term Eff
instance Subst Term Effect
instance Subst Term ADTBody
instance Subst Term CaseCls
instance Subst Term Pattern

instance Subst Term Term where
  isvar (Var x)  =  Just (SubstName x)
  isvar _        =  Nothing

isVal :: Term -> Bool
isVal Var{}      = True
isVal Lam{}      = True
isVal LamCase{}  = True
isVal LamCaseAnno{} = True
isVal TAbs{}     = True    -- parser checks value restriction of TAbs
isVal (Anno m _) = isVal m
isVal App{}      = False
isVal (TApp m _) = isVal m
isVal Let{}      = False
isVal LetRec{}   = False
isVal Do{}       = False
isVal Mask{}     = False
isVal Handle{}   = False
isVal TmInt{}    = True
isVal TmChar{}    = True
isVal Expr{}     = False
isVal If{}       = False
isVal (Cons _ ms) = all isVal ms
isVal (CasePat [] (([], CaseTerm m):_)) = isVal m
isVal CasePat{}  = False
isVal Fix{}      = True
isVal Dor{}      = False
isVal Print{}    = False
isVal tm         = error $ "isVal: do not support" ++ show tm

getInfo :: Term -> Info
getInfo (IVar         info _)   = info
getInfo (ILam         info _)   = info
getInfo (ILamCase     info _)   = info
getInfo (ILamCaseAnno info _ _) = info
getInfo (IAnno        info _ _) = info
getInfo (IApp         info _ _) = info
getInfo (ITApp        info _ _) = info
getInfo (ILet         info _ _) = info
getInfo (ILetRec      info _ _) = info
getInfo (IDo          info _ _) = info
getInfo (IMask        info _ _) = info
getInfo (ITAbs        info _ _) = info
getInfo (ICons        info _ _) = info
getInfo (ICasePat     info _ _) = info
getInfo (ITmInt       info _)   = info
getInfo (ITmChar      info _)   = info
getInfo (IExpr        info _ _ _) = info
getInfo (IIf          info _ _ _) = info
getInfo (IHandle      info _ _ _) = info
getInfo (IPrint       info _)   = info
getInfo (Fix          _)        = None
getInfo Dor{}                   = None

-- only for runtime
getOps :: HandlerClauses -> Effect
getOps = row2eff . map ((`Eff` []) . fst) . filter ((/= "return") . fst)

-- | Return True if do calculation, otherwise comparison
isCalc :: String -> Bool
isCalc "+" = True
isCalc "-" = True
isCalc _   = False

-- * Shapes

data Shape
  = Hole
  | Check Type
  | GArr Shape
  --  | GPair Bool Shape
  --  | GADT  -- G means guarded not generalised
  deriving (Generic, Show)
-- We do not need guarded forall because we can only instantiate variables.

-- * Contexts

type Context = Bwd Entry
data Entry
  = TmVar   (Name Term) Type (Maybe Term)
  | Lock    Type
  | TyVar   (Name Type) Kind
  | IDefADT Info ADTType
  | IDefEff Info EffectType
  --  | IDefEff Info (Label, Type, Type)
  deriving (Show, Generic)
instance Alpha Entry

pattern DefADT :: (ADTName, Bind (Name Type) ADTBody) -> Entry
pattern DefADT namebnd <- IDefADT _ namebnd where
  DefADT namebnd = IDefADT None namebnd
pattern DefEff :: EffectType -> Entry
pattern DefEff eff <- IDefEff _ eff where
  DefEff eff = IDefEff None eff

builtinCtx :: Context
builtinCtx = Nil
  :< DefADT ("Unit", bind (s2n "Unit") $ ADTCons [("unit", [])])
  :< DefADT ("Bool", bind (s2n "Bool") $ ADTCons [("true", []), ("false", [])])
  :< DefADT ("Pair", bind (s2n "Pair") . ADTBind Any . bind (s2n "a") . ADTBind Any . bind (s2n "b") $
                     ADTCons [("pair", [TVar (s2n "a"), TVar (s2n "b")])])
  :< DefADT ("List", bind (s2n "List") . ADTBind Any . bind (s2n "a") $
                     ADTCons [ ("nil", [])
                             , ("nils", []) -- nil for string
                             , ("cons", [TVar (s2n "a"), TVar (s2n "List")])])

builtinConsNames :: [(Label, Int)]
builtinConsNames =
  [ ("unit", 0)
  , ("true", 0)
  , ("false", 0)
  , ("pair", 2)
  , ("nil", 0)
  , ("cons", 2)
  , ("nils", 0)
  ]

equalCons :: Label -> Label -> Bool
equalCons "nil" "nils" = True
equalCons "nils" "nil" = True
equalCons x      y     = x == y

tmVar :: Name Term -> Type -> Entry
tmVar x sigma = TmVar x sigma Nothing

instance Eq Entry where
  (==) = aeq

ityUnit :: Info -> Type
ityUnit info = IADT info "Unit" []

tyUnit :: Type
tyUnit = ADT "Unit" []

tmUnit :: Term
tmUnit = Cons "unit" []

tyBool :: Type
tyBool = ADT "Bool" []

tmTrue :: Term
tmTrue = Cons "true" []

tmFalse :: Term
tmFalse = Cons "false" []

ityPair :: Info -> Type -> Type -> Type
ityPair info a b = IADT info "Pair" [a, b]

tyPair :: Type -> Type -> Type
tyPair a b = ADT "Pair" [a, b]

newtype Contextual a = Contextual
    (StateT Context (FreshMT (ExceptT String Identity)) a)

deriving instance Applicative Contextual
deriving instance Alternative Contextual
deriving instance Functor Contextual
deriving instance Monad Contextual
deriving instance MonadState Context Contextual
deriving instance MonadError String Contextual
deriving instance Fresh Contextual

instance MonadFail Contextual where
  fail s = throwError ("MonadFail: " ++ s)

runContextual :: Context -> Contextual a -> Either String (a, Context)
runContextual mcx (Contextual m) = runIdentity . runExceptT . runFreshMT . flip runStateT mcx $ m

indent :: String -> String
indent = unlines . map ("  " ++) . lines

reThrow :: Contextual a -> String -> Contextual a
reThrow m s = catchError m (\ e -> throwError (s ++ "\nIn the call of\n" ++ indent e))

wrapMaybe :: Maybe a -> String -> Contextual a
wrapMaybe Nothing x = throwError x
wrapMaybe (Just x) _  = return x

-- | Return argument numbers of ADT by name
argNumADT :: MonadError String m => Context -> ADTName -> m Int
argNumADT ctx name = help ctx
  where
    help :: MonadError String m => Context -> m Int
    help Nil = throwError $ "Datatype " ++ show name ++ " not defined."
    help (_ :< DefADT (name', adtbody)) | name' == name  =
      return . runFreshM $ do (_, body) <- unbind adtbody; countArgs body
    help (ctx' :< _) = help ctx'
    countArgs :: Fresh m => ADTBody -> m Int
    countArgs (ADTCons _) = return 0
    countArgs (ADTBind _ bnd) = do
      (_, body) <- unbind bnd
      (1 +) <$> countArgs body
