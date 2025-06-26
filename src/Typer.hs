{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Typer (module Typer) where

import Prelude hiding (pi, elem)

import Control.Monad
import Control.Monad.Except (throwError, catchError)
import Control.Monad.State
import Data.List (find, isPrefixOf, tails, nub)

import Unbound.Generics.LocallyNameless
import BwdFwd ( Bwd((:<), Nil) )
import Syntax
import Printer

-- import Debug.Trace

-- * Error messages

data ErrorKind =
    KindMismatch Type Kind Kind
  | KindImpossible Type Kind
  | IllFormedType Type
  | NoVarAccess Term Type Type Effect
  | NoModTrans Type Type Effect
  | NoModTyTrans (Type, Type) Type Effect
  | ArgNumMismatch
  | AnnoMismatch [Type] [Type]
  | TypeMismatch Type Type
  | NotArrow Type
  | NotMask Type
  | MaskMismatch Effect Type
  | ConsArgMismatch [Type] [Term]
  | TypeFail Term Shape
  | TermVarNotFound Term
  | TypeVarNotFound Type
  | OpNotFound Label
  | LabelNotFound Label
  | NameNotFound String
  | NonUniqueOp Label
  | InstMismatch Type
  | OtherTypeError String
  | Impossible String
  | EffectNotPresent EffectName
  | EffectNotWellFormed EffectName
  | EffectNotEnoughArgs EffectName

showPos :: Info -> String
showPos None = ""
showPos (Info (s, line, column)) = s ++ ":" ++ show line ++ ":" ++ show column ++ ": "

errMsg :: Info -> ErrorKind -> String
errMsg info (KindMismatch ty k1 k2) = showPos info
  ++ "Kind error: type " ++ showType ty ++ " has kind " ++ show k1
  ++ " but expect " ++ show k2
errMsg info (KindImpossible ty k) = showPos info
  ++ "Kind error: type " ++ showType ty ++ " cannot have kind " ++ show k
errMsg info (IllFormedType ty) = showPos info
  ++ "Kind error: type " ++ showType ty ++ " is ill-formed"
errMsg info (Impossible s) = showPos info ++ "Impossible error: " ++ s
errMsg info (NoVarAccess var ty nu e) = showPos info
  ++ "Type error: variable " ++ showValue var ++ " of type " ++ showType ty
  ++ " cannot be accessed under modality " ++ showType nu ++ " at effect context " ++ showEffect e
  ++ " nomatter however unboxed"
errMsg info (NoModTrans mu nu e) = showPos info
  ++ "Type error: cannot transform modality " ++ showType mu ++ " to " ++ showType nu
  ++ " at effect context " ++ showEffect e
errMsg info (NoModTyTrans (mu, g) nu e) = showPos info
  ++ "Type error: cannot transform modality " ++ showType mu ++ " to " ++ showType nu
  ++ " for type " ++ showType (Mod mu g) ++ " at effect context " ++ showEffect e
errMsg info (OtherTypeError s) = showPos info
  ++ "Type error: " ++ s
errMsg info (AnnoMismatch as bs) = showPos info
  ++ "Type error: annotations require " ++ show as ++ " but given " ++ show bs
errMsg info ArgNumMismatch = showPos info
  ++ "Type error: argument number does not match the function type"
errMsg info (NotArrow ty) = showPos info
  ++ "Type error: " ++ showType ty ++ " ought to be a function type"
errMsg info (NotMask ty) = showPos info
  ++ "Type error: " ++ showType ty ++ " is not a mask type"
errMsg info (MaskMismatch l ty) = showPos info
  ++ "Type error: masking " ++ show l ++ " does not match the modality " ++ showType ty
errMsg info (ConsArgMismatch as ms) = showPos info
  ++ "Type error: constructor arguments expect " ++ show (length as)
  ++ " arguments, but is given " ++ show (length ms) ++ " arguments"
errMsg info (TypeMismatch a b) = showPos info
  ++ "Type error: expect type " ++ showType a ++ " but got type " ++ showType b
errMsg info (TypeFail m s) = showPos info
  ++ "Type error: cannot type check " ++ showValue m ++ " with shape " ++ show s
errMsg info (TermVarNotFound tm) = showPos info
  ++ "Type error: term variable " ++ showValue tm ++ " not bound"
errMsg info (TypeVarNotFound ty) = showPos info
  ++ "Type error: type variable " ++ showType ty ++ " not bound"
errMsg info (OpNotFound l) = showPos info
  ++ "Type error: operation " ++ l ++ " not defined"
errMsg info (LabelNotFound l) = showPos info
  ++ "Type error: label " ++ l ++ " is not defined as either a constructor or an operation"
errMsg info (NameNotFound l) = showPos info
  ++ "Type error: name " ++ l ++ " is not defined as either an ADT or an effect"
errMsg info (NonUniqueOp l) = showPos info
  ++ "Type error: operation " ++ l ++ " has been defined"
errMsg info (InstMismatch ty) = showPos info
  ++ "Type error: cannot instantiate " ++ showType ty
errMsg info (EffectNotPresent effname) = showPos info
  ++ "Type error: effect " ++ effname ++ " is not present in the effect context"
errMsg info (EffectNotWellFormed effname) = showPos info
  ++ "Type error: effect " ++ effname ++ " is not well-formed in the effect context"
errMsg info (EffectNotEnoughArgs effname) = showPos info
  ++ "Type error: effect " ++ effname ++ " does not take enough arguments in the effect context"

raiseError :: Info -> ErrorKind -> Contextual a
raiseError info err = throwError $ errMsg info err


-- * Auxiliary functions

-- | Find the type of and the locks right to a term variable.
findTm :: Term -> Contextual (Type, Type)
findTm tm@(IVar info x) = get >>= help
  where
    help :: Context -> Contextual (Type, Type)
    help Nil                              = raiseError info $ TermVarNotFound tm
    help (_ :< TmVar y sigma _) | x == y  = return (sigma, one)
    help (ctx :< Lock nu)                 = help ctx >>= \ (sigma, mu) -> return (sigma, mu <> nu)
    help (ctx :< _)                       = help ctx
findTm _ = raiseError None (Impossible "")

-- | Find the kind of a rigid type variable
findTy :: Type -> Contextual Kind
findTy ty@(ITVar info a) = get >>= help
  where
    help :: Context -> Contextual Kind
    help Nil                        = raiseError info $ TypeVarNotFound ty
    help (_ :< TyVar b k) | a == b  = return k
    help (ctx :< _)                 = help ctx
findTy _ = raiseError None (Impossible "")

-- | Run a computation with an additional entry, then remove it.
withEntry :: Entry -> Contextual a -> Contextual a
-- withEntry e m = do modify (:< e)
--                    a <- m
--                    _ <- popR
--                    return a
withEntry e m = do modify (:< e)
                   a <- m
                   modify dropEntry
                   return a
  where
    dropEntry Nil = error "impossible"
    dropEntry (mcx :< e') | e' == e = mcx
                          | otherwise = dropEntry mcx :< e'

withEntries :: [Entry] -> Contextual a -> Contextual a
withEntries es m = foldr withEntry m es

-- | Pop an entry from the right.
popR :: Contextual Entry
popR = do mcx :< e <- get
          put mcx
          return e


-- * Kinding

kind :: Type -> Kind -> Contextual ()
kind ty@(ITVar info _) k = do
  k' <- findTy ty
  if k' <= k then return ()
  else raiseError info $ KindMismatch ty k' k
kind ty@(IArr info a b) k
  | k == Any  =  kind a Any >> kind b Any
  | otherwise =  raiseError info $ KindImpossible ty k
kind ty@(IMod info (Rel _ _) a) k =
  if k == EffectKind then raiseError info $ KindImpossible ty k
  else kind a k
kind ty@(IMod info (Abs _) a) k =
  if k == EffectKind then raiseError info $ KindImpossible ty k
  else kind a Any
kind ty@(IMod info _ _) _ = raiseError info $ IllFormedType ty
kind ty@(IAbs info _)   _ = raiseError info $ IllFormedType ty
kind ty@(IRel info _ _) _ = raiseError info $ IllFormedType ty
kind ty@(IAll info k' bnd) k =
  if k == EffectKind then raiseError info $ KindImpossible ty k
  else do (alpha, sigma) <- unbind bnd
          withEntry (TyVar alpha k') (kind sigma k)
kind ty@(ITInt info) k  = when (k == EffectKind) $ raiseError info $ KindImpossible ty k
kind ty@(ITChar info) k = when (k == EffectKind) $ raiseError info $ KindImpossible ty k
kind ty@(IADT info name _) k = do
  adt <- name2ADT name
  k' <- kindadt ty adt
  unless (k' <= k) $ raiseError info $ KindImpossible ty k
-- kind ty _ = throwError $ "kind: Cannot check the kind of " ++ show ty

kindadt :: Type -> ADTType -> Contextual Kind
kindadt (ADT _ tys) (_, bnd) = do
  -- Names are guaranteed to match.
  body <- subst' tyUnit bnd
  ADTCons conslist <- instADT body tys
  let tylist = concatMap snd conslist
  checks <- mapM (`kindCheck` Pure) tylist
  if and checks then return Pure
  else return Any
kindadt _ _ = raiseError None (Impossible "") -- guaranteed to be ADT

contains :: Eq a => [a] -> [a] -> Bool
contains str substr = any (isPrefixOf substr) (tails str)

kindCheck :: Type -> Kind -> Contextual Bool
kindCheck a k = (kind a k >> return True) `catchError` (\s ->
  if (s `contains` "Kind error:") && not (s `contains` "ill-formed") then return False
  else throwError s)


-- | Return the type for each argument and the result
unrollArr :: Info -> Int -> Type -> Contextual ([Type], Type)
unrollArr _    0 res = return ([], res)
unrollArr info n (arg `Arr` res) = do (as, res') <- unrollArr info (n - 1) res; return (arg:as, res')
unrollArr info _ _ = raiseError info ArgNumMismatch

modTyTrans :: (Type, Type) -> Type -> Effect -> Contextual Bool
modTyTrans (mu, g) nu e = do
  isPure <- kindCheck g Pure
  if isPure then return True
  else return (modTrans mu nu e)

-- | Instantiation
inst :: Info -> Type -> [Type] -> Contextual Type
inst _ a [] = return a
inst info (All k bnd) (a:as) = do
  kind a k
  (alpha, b) <- unbind bnd
  inst info (subst alpha a b) as
inst info a (_:_) = raiseError info $ InstMismatch a

-- | Split the top-level modalit(ies) from a type
split :: Type -> Contextual (Type, Type)
split (Mod mu a) = do
  (nu, b) <- split a
  return (mu <> nu, b)
split a = return (one, a)

splitAbs :: Type -> Contextual ([(Name Type, Kind)], Type)
splitAbs (All k bnd) = do
  (alpha, a) <- unbind bnd
  (alphas, b) <- splitAbs a
  return ((alpha, k):alphas, b)
splitAbs a = return ([], a)

combineAbs :: [(Name Type, Kind)] -> Type -> Contextual Type
combineAbs [] a = return a
combineAbs ((alpha, k):alphas) b = do
  res <- combineAbs alphas b
  return $ All k (bind alpha res)

-- | The across function used in T-Var
across :: Term -> Info -> Type -> Type -> Effect -> Contextual Type
across var info a nu f = do
  isPure <- kindCheck a Pure
  if isPure then return a
  else do
    (alphas, b) <- splitAbs a
    (mu, g) <- split b
    res <- rightResidual nu mu f
    case res of
      Just xi -> combineAbs alphas (Mod xi g)
      Nothing -> raiseError info $ NoVarAccess var a nu f
    -- Old version without considering commuting top-level modalities inside:
    -- (mu, g) <- split a
    -- xi <- rightResidual nu mu f
    -- return (Mod xi g)

-- `rightResidual nu mu f` gives `xi` if `xi_{nu(f)} = nu_f \ mu_f`
--    which is equivalent to `mu => nu ∘ xi @ f`
rightResidual :: Type -> Type -> Effect -> Contextual (Maybe Type)
rightResidual _ (Abs e) _ = return . Just $ Abs e
rightResidual (Rel l' d') (Rel l d) f =
  if (l' -: l) <: f then return . Just $ Rel (d' +: (l -: l')) (d +: (l' -: l))
  else return Nothing
rightResidual _ _ _ = return Nothing


-- Join the top-level modalities of two types
joinType :: Type -> Type -> Effect -> Contextual Type
joinType a b e = do
  (mu, g1) <- split a
  (nu, g2) <- split b
  unless (g1 == g2) $ throwError "joinType: Type mismatch."
  isPure <- kindCheck g1 Pure
  if isPure then return g1
  else do xi <- joinMod mu nu e
          return (Mod xi g1)

-- Join two modalities
joinMod :: Type -> Type -> Effect -> Contextual Type
joinMod (Abs e) (Abs e') _ = case e \/ e' of
  Just f -> return $ Abs f
  Nothing -> throwError "joinMod: Effect combination failed."
joinMod (Abs e) (Rel l d) f =
  if e <: (d +: (f -: l)) then return $ Rel l d
  else throwError "joinMod: fail."
joinMod r1@(Rel l d) r2@(Rel l' d') f = case (l /\ l', d /\ d') of
  (Just l'', Just d'') ->
    let r = Rel l'' d'' in
    if modTrans r1 r f && modTrans r2 r f then return r
    else throwError "joinMod: fail."
  _ -> throwError "joinMod: fail." -- should be impossible
joinMod _ _ _= throwError "joinMod: fail."


-- * Bidirectional Type Checking

-- | Box non-pure global definitions
preCtx :: Context -> Contextual Context
preCtx Nil = return Nil
preCtx (ctx :< TmVar name ty tm) = do
  ctx' <- preCtx ctx
  isPure <- kindCheck ty Pure
  if isPure then return (ctx' :< TmVar name ty tm)
  else return $ ctx' :< TmVar name (Mod (Abs En) ty) tm
preCtx (ctx :< entry) = do
  ctx' <- preCtx ctx
  return $ ctx' :< entry


-- Type check a global context.
typCtx :: Context -> Contextual (Context, [(String, Type)])
typCtx Nil               = return (Nil, [])
typCtx (_ :< Lock _)     = raiseError None $ Impossible "Lock in the global context."
typCtx (_ :< TyVar _ _)  = raiseError None $ Impossible "TyVar in the global context."
typCtx (ctx :< DefADT adt@(_, bnd)) = do
  (ctx', res) <- typCtx ctx
  (alpha, body) <- unbind bnd
  (alphas, ADTCons conslist) <- unwrapADT body
  let tylist = concatMap snd conslist
  put ctx'
  withEntries (map (uncurry TyVar) ((alpha, Any):alphas)) $ mapM_ (`kind` Any) tylist
  uniqueADT adt -- check uniqueness of names and labels
  return (ctx' :< DefADT adt, res)
typCtx (ctx :< IDefEff info eff@(_, effbody)) = do
  (ctx', res) <- typCtx ctx
  (alphas, ADTCons oplist) <- unwrapADT effbody
  let tylist = concatMap snd oplist
  put ctx'
  withEntries (map (uncurry TyVar) alphas) $ mapM_ (`kind` Pure) tylist
  uniqueEFF eff
  return (ctx' :< IDefEff info eff, res)
typCtx (ctx :< TmVar name ty (Just tm)) = do
  (ctx', res) <- typCtx ctx
  put ctx'
  isPure <- kindCheck ty Pure
  let ty' = if isPure then ty else Mod (Abs En) ty
    -- Add the potentially omitted [] modality for variable bindings in the global context.
  a <- typWith (ctx' :< TmVar name ty' (Just tm)) tm (Check ty') En
    -- Global context must be at empty effect context.
  return (ctx' :< TmVar name ty' (Just tm), res ++ [(name2String name, a)])
typCtx _ = raiseError None (OtherTypeError "cannot type check the global context.")

typWith :: Context -> Term -> Shape -> Effect -> Contextual Type
typWith ctx m s e = put ctx >> typ m s e

typ :: Term -> Shape -> Effect -> Contextual Type
-- B-Var
typ var@(IVar info _) Hole e = do
  (a, nu) <- findTm var
  let f = nu |> e
  across var info a nu f
-- B-TApp
typ (ITApp info m a) Hole e = do
  ty <- typ m Hole e
  (mu, sigma) <- split ty
  canTrans <- modTyTrans (mu, sigma) one e
  unless canTrans $ raiseError info $ NoModTyTrans (mu, sigma) one e
  inst info sigma [a]
-- B-Annotation
typ (Anno v a) Hole e = do
  kind a Any
  typ v (Check a) e
-- B-Forall
typ (ITAbs info k bnd) (Check (All k' bnd')) e = do
  -- Always require term-level type abstraction
  (alpha, a) <- unbind bnd'
  unless (k == k') $ raiseError info $ KindMismatch (TVar alpha) k k'
  v <- subst' (TVar alpha) bnd
  _ <- withEntry (TyVar alpha k) $ typ v (Check a) e
  return (All k bnd')
typ (TAbs k bnd) Hole e = do
  (alpha, v) <- unbind bnd
  a <- withEntry (TyVar alpha k) $ typ v Hole e
  return (All k (bind alpha a))
-- B-Mod
typ v (Check (Mod mu a)) e | isVal v = do
  _ <- withEntry (Lock mu) $ typ v (Check a) (mu |> e)
  return (Mod mu a)
-- B-Abs
typ (Lam bnd) (Check (a `Arr` b)) e = do
  (x, m) <- unbind bnd
  _ <- withEntry (tmVar x a) (typ m (Check b) e)
  return (a `Arr` b)
typ (ILamCase info casecls) (Check (a `Arr` b)) e = do
  len <- argNum casecls
  (as, res) <- unrollArr info len (a `Arr` b)
  _ <- typcasepat as [casecls] (Check res) e
  return (a `Arr` b)
typ (ILamCaseAnno info annos casecls) (Check (a `Arr` b)) e = do
  len <- argNum casecls
  (as, res) <- unrollArr info len (a `Arr` b)
  when (annos /= as) $ raiseError info $ AnnoMismatch annos as
  _ <- typcasepat as [casecls] (Check res) e
  return (a `Arr` b)
typ (ILamCaseAnno info annos casecls) Hole e = do
  len <- argNum casecls
  when (len /= length annos) $ raiseError info ArgNumMismatch
  res <- typcasepat annos [casecls] Hole e
  return $ foldr Arr res annos
-- typ (LamAnno a bnd) s e = do
--   (s1, s2) <- toArr s
--   a' <- a ~~ s1
--   (x, m) <- unbind bnd
--   b <- withEntry (tmVar x a) (typ m s2 e)
--   return (a' `Arr` b)
-- B-App
typ (IApp info m n) Hole e = do
  a <- typ m Hole e
  (mu, a') <- split a
  unless (modTrans mu one e) $ raiseError info $ NoModTrans mu one e
  case a' of
    a1 `Arr` a2 -> typ n (Check a1) e >> return a2
    t -> raiseError info $ NotArrow t
typ (Let m bnd) s e = do
  a <- typ m Hole e
  (x, n) <- unbind bnd
  withEntry (tmVar x a) (typ n s e)
typ (LetRec a bnd) s e = do
  (x, (m, n)) <- unbind bnd
  withEntry (tmVar x a) $ do
    _ <- typ m (Check a) e
    typ n s e
-- B-Do
typ (IDo info op m) Hole e = do
  (a, b) <- opType info op e
  _ <- typ m (Check a) e
  return b
-- B-MaskInfer
typ (Mask l m) Hole e = do
  a <- withEntry (Lock (Rel l En)) (typ m Hole (e -: l))
  return (Mod (Rel l En) a)
-- B-MaskCheck
typ (IMask info l m) (Check a) e = do
  -- Another option: if fails, should at least try B-Switch
  isPure <- kindCheck a Pure
  if isPure then withEntry (Lock (Rel l En)) (typ m (Check a) (e -: l))
  else case a of
    Mod (Rel l' En) a' -> do
      unless (l == l') $ raiseError info $ MaskMismatch l (Rel l' En)
      _ <- withEntry (Lock (Rel l En)) (typ m (Check a') (e -: l))
      return a
    _ -> raiseError info (NotMask a)
-- B-HandleCheck/Infer
typ (Handle (Just eff) m h) s e = do
  let d = eff
  a <- withEntry (Lock (Rel En d)) (typ m Hole (d +: e))
  typh (Mod (Rel En d) a) eff h s e
typ (IHandle info Nothing m h) s e = do
  effnames <- mapM (label2effname info . fst) $ filter ((/= "return") . fst) h
  let eff = foldr (Ec . (`Eff` [])) En $ nub effnames
  let d = eff
  a <- withEntry (Lock (Rel En d)) (typ m Hole (d +: e))
  typh (Mod (Rel En d) a) eff h s e
-- ADT
typ (ICons info cons ms) (Check adt) e = do
  -- Cons requires checking mode for simplicity
  as <- consType cons adt
  when (length as /= length ms) . raiseError info $ ConsArgMismatch as ms
  mapM_ (\ (m, a) -> typ m (Check a) e) (zip ms as)
  return adt
typ (ICasePat info ms patcls) s e = case patcls of
  [] -> raiseError info $ OtherTypeError "Empty case clause."
  ((_, _):_) -> do
    as <- mapM (\ m -> typ m Hole e) ms
    typcasepat as patcls s e
-- base types
typ (Cons "unit" []) Hole _ =
  -- Optimise inference for units.
  -- This is really a hack. I assume the preclude always defines unit.
  return tyUnit
typ (Cons "true" []) Hole _ =
  return tyBool
typ (Cons "false" []) Hole _ =
  return tyBool
typ (TmInt _) Hole _ = do
  return TInt
typ (TmChar _) Hole _ = do
  return TChar
typ (Expr opr m n) Hole e = do
  let resty = if isCalc opr then TInt else tyBool
  _ <- typ m (Check TInt) e
  _ <- typ n (Check TInt) e
  return resty
typ (If b m n) s e = do
  _ <- typ b (Check tyBool) e
  a1 <- typ m s e
  a2 <- typ n s e
  joinType a1 a2 e
typ (Print _) Hole _ = return tyUnit
-- B-Switch
typ m (Check a) e = do
  let info = getInfo m
  b <- typ m Hole e
  (mu, g1) <- split b
  (nu, g2) <- split a
  when (g1 /= g2) $ raiseError info $ TypeMismatch g2 g1
  canTrans <- modTyTrans (mu, g1) nu e
  unless canTrans $ raiseError info $ NoModTyTrans (mu, g1) nu e
  return a
typ m s _ = do
  let info = getInfo m
  raiseError info $ TypeFail m s

-- The first argument is the return type of the handled computation boxed by the extension modality.
typh :: Type -> Effect -> HandlerClauses -> Shape -> Effect -> Contextual Type
typh _ _ [] _ _ = raiseError None $ Impossible "empty or none-return handler"
typh resty _ [("return", casecls)] s e = typcasepat [resty] [casecls] s e
typh resty eff ((op, casecls):clss) s e = do
  b <- typh resty eff clss s e
  (ai, bi) <- opType None op (eff +: e)
  b' <- typcasepat [ai, bi `Arr` b] [casecls] s e
  joinType b b' e

unbinds :: CaseCls -> Contextual ([Name Term], Term)
unbinds (CaseTerm m) = return ([], m)
unbinds (CaseBind bnd) = do
  (x, m) <- unbind bnd
  (xs, n) <- unbinds m
  return (x:xs, n)


-- | The first argument gives the types of the pattern in each clause.
typcasepat :: [Type] -> CasePatClauses -> Shape -> Effect -> Contextual Type
typcasepat _ [] _ _ = throwError "typcasepat: Empty case clause."
typcasepat tys ((pats, casecls):cls) s e = do
  as <- findPatTypes tys pats
  (xs, m) <- unbinds casecls
  b <- foldl (\ t (x, a) -> withEntry (tmVar x a) t) (typ m s e) (zip xs as)
  case cls of
    [] -> return b
    _  -> do b' <- typcasepat tys cls s e
             joinType b b' e


-- * Utilities for ADT

-- | Shorthand for type substitution
subst' :: (Alpha a, Subst Type a) => Type -> Bind (Name Type) a -> Contextual a
subst' x bnd = do
  (alpha, body) <- unbind bnd
  return $ subst alpha x body

instADT :: ADTBody -> [Type] -> Contextual ADTBody
instADT body tys = do
  go body tys
  where
    go :: ADTBody -> [Type] -> Contextual ADTBody
    go (ADTCons conslist) [] = return $ ADTCons conslist
    go (ADTBind _ bnd') (a:as) = do
      body' <- subst' a bnd'
      go body' as
    go _ _ = throwError "instADT: Arguments mismatch."

instEff :: ADTBody -> [Type] -> Contextual ADTBody
instEff = instADT

-- | Return the list of parameters and ADT body.
unwrapADT :: Fresh m => ADTBody -> m ([(Name Type, Kind)], ADTBody)
unwrapADT (ADTCons conslist) = return ([], ADTCons conslist)
unwrapADT (ADTBind k bnd) = do
  (alpha, body) <- unbind bnd
  (alphas, body') <- unwrapADT body
  return ((alpha,k):alphas, body')

-- | Given a type and a pattern, find the types for all variables in the pattern.
findPatType :: Type -> Pattern -> Contextual [Type]
findPatType a PVar    = return [a]
findPatType a PChar{} = do
  when (a /= TChar) $ throwError "findPatType: Char pattern does not match type."
  return [] -- no variable
findPatType a PInt{}  = do
  when (a /= TInt) $ throwError "findPatType: Int pattern does not match type."
  return [] -- no variable
findPatType a b@(PCons cons patlist) = do
  (mu, a') <- split a -- Crispy
  case a' of
    (ADT name _) -> do
      conslist <- adt2conslist a'
      case find (equalCons cons . fst) conslist of
        Nothing -> throwError $ "ADT " ++ name ++ " does not have constructor " ++ cons
        Just (_, tylist) -> do
          res <- forM (zip patlist tylist) $ \ (pat, ty) -> findPatType (Mod mu ty) pat
          return (concat res)
    _ -> throwError $ "findPatType: " ++ show a ++ " is not a type for pattern " ++ show b

-- | Given the type and pattern of each term, find the types for all
--   variables in the pattern
findPatTypes :: [Type] -> [Pattern] -> Contextual [Type]
findPatTypes [] [] = return []
findPatTypes (a:as) (p:ps) = do
  res <- findPatType a p
  rest <- findPatTypes as ps
  return (res ++ rest)
findPatTypes _ _ = throwError "findPatTypes: Arguments mismatch."

-- | Given an ADT type, return its constructors with their argument types.
adt2conslist :: Type -> Contextual [(Label, [Type])]
adt2conslist adt@(ADT name tys) = do
  (_, adtbnd) <- name2ADT name
  adtbody <- subst' adt adtbnd
  ADTCons conslist <- instADT adtbody tys
  return conslist
adt2conslist _ = throwError "adt2conslist: Not an ADT."

-- | Given constructor name and ADT type, find the type of the arguments of the given constructor.
consType :: Label -> Type -> Contextual [Type]
consType cons adt = do
  conslist <- adt2conslist adt
  case find (equalCons cons . fst) conslist of
    Nothing -> throwError $ "Constructor " ++ cons ++ " is not present in the ADT."
    Just (_, tys) -> return tys

-- | Find an ADT definition by its name.
name2ADT :: ADTName -> Contextual ADTType
name2ADT name = name2entry name >>= \case
  DefADT adt -> return adt
  _ -> throwError $ "name2ADT: " ++ name ++ " is not an ADT."

-- | Given operation name and effect context, find the type of given operation.
opType :: Info -> Label -> Effect -> Contextual (Type, Type)
opType info op e = label2entry op >>= \case
  DefEff (effname, effbody) ->
    case find ((== effname) . effName) (eff2row e) of
      Just (Eff _ tyargs) -> instEff effbody tyargs >>= \case
        ADTCons oplist -> case find ((== op) . fst) oplist of
          Just (_, [a, b]) -> return (a, b)
          Just (_, _) -> raiseError info $ EffectNotWellFormed effname
          Nothing -> raiseError info $ Impossible ""
        _ -> raiseError info $ EffectNotEnoughArgs effname
      Nothing -> raiseError info $ EffectNotPresent effname
  _ -> raiseError info $ OpNotFound op

label2entry :: Label -> Contextual Entry
label2entry l = get >>= help
  where
    help :: Context -> Contextual Entry
    help Nil = raiseError None $ LabelNotFound l
    help (ctx :< entry@(DefADT adt)) = do
      case find (l ==) (adt2labels adt) of
        Nothing -> help ctx
        Just _  -> return entry
    help (ctx :< entry@(DefEff eff)) = do
      case find (l ==) (eff2labels eff) of
        Nothing -> help ctx
        Just _  -> return entry
    help (ctx :< _) = help ctx

name2entry :: String -> Contextual Entry
name2entry name = get >>= help
  where
    help :: Context -> Contextual Entry
    help Nil = raiseError None $ NameNotFound name
    help (_ :< entry@(DefADT (adtname, _))) | adtname == name = return entry
    help (_ :< entry@(DefEff (effname, _))) | effname == name = return entry
    help (ctx :< _) = help ctx

label2effname :: Info -> Label -> Contextual EffectName
label2effname info op = do
  entry <- label2entry op
  case entry of
    DefEff (effname, _) -> return effname
    _ -> raiseError info $ OpNotFound op

adt2labels :: ADTType -> [Label]
adt2labels (_, bnd) = runFreshM $ do
  (_, body) <- unbind bnd
  unwrapADT body >>= (\case
    ADTCons conslist -> return (map fst conslist)
    _ -> error "impossible") . snd

eff2labels :: EffectType -> [Label]
eff2labels (_, body) = runFreshM $ do
  unwrapADT body >>= (\case
    ADTCons conslist -> return (map fst conslist)
    _ -> error "impossible") . snd

-- | Check the uniqueness conditions of ADT definitions:
--   1. The ADT name must be unique.
--   2. The constructor labels must be unique.
uniqueADT :: ADTType -> Contextual ()
uniqueADT adt@(name, _) = do
  let conslabels = adt2labels adt
  when (null conslabels) $ throwError "uniqueADT: Empty ADT is not allowed."
  (name2entry name >> throwError "uniqueADT: ADT name is not unique.") `catchError` \_ -> return ()
  mapM_ (\l -> (label2entry l >> throwError "uniqueADT: Constructor label is not unique.")
                  `catchError` \_ -> return ()) conslabels

uniqueEFF :: EffectType -> Contextual ()
uniqueEFF eff@(name, _) = do
  let oplabels = eff2labels eff
  when (null oplabels) $ throwError "uniqueEFF: Empty effect is not allowed."
  (name2entry name >> throwError "uniqueEFF: effect name is not unique.") `catchError` \_ -> return ()
  mapM_ (\l -> (label2entry l >> throwError "uniqueEFF: operation name is not unique.")
                  `catchError` \_ -> return ()) oplabels