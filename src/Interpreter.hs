{-# LANGUAGE TupleSections #-}
module Interpreter (module Interpreter) where


import Syntax
import Unbound.Generics.LocallyNameless
import Control.Monad.Except (throwError)
import Control.Monad.State
import Helper (var, tmb)
import BwdFwd
-- import Debug.Trace
import Control.Monad.Writer
import Data.Foldable (find)

type Runtime a = WriterT String Contextual a

-- * Type erasure

rewrap :: (Fresh m, Alpha p, Alpha t1, Alpha t2) => (t1 -> m t2) -> Bind p t1 -> m (Bind p t2)
rewrap f bnd = do
  (x, body) <- unbind bnd
  body' <- f body
  return $ bind x body'

erase :: Term -> Contextual Term
erase (Var x) = return $ Var x
erase (Lam bnd) = Lam <$> rewrap erase bnd
erase (LamCase casecls) = LamCase <$> eraseCase casecls
-- erase (LamCaseAnno _ bnd) = Lam <$> rewrap erase bnd
erase (LamCaseAnno _ casecls) = LamCase <$> eraseCase casecls
erase (Anno m _) = erase m
erase (App m n) = App <$> erase m <*> erase n
erase (Let m bnd) = Let <$> erase m <*> rewrap erase bnd
erase (LetRec a bnd) = LetRec a <$> rewrap (\(m, n) -> (,) <$> erase m <*> erase n) bnd
erase (Do l m) = Do l <$> erase m
erase (Mask e m) = Mask e <$> erase m
erase (Handle _ m h) = Handle Nothing <$> erase m <*> eraseHandler h
erase (TAbs _ bnd) = do
  (_, body) <- unbind bnd
  erase body
erase (TApp m _) = erase m
erase (Cons l ms) = Cons l <$> mapM erase ms
erase (CasePat ms casecls) = do
  ms' <- mapM erase ms
  casecls' <- eraseCases casecls
  return $ CasePat ms' casecls'
erase (TmInt n)  = return $ TmInt n
erase (TmChar c) = return $ TmChar c
erase (Expr opr m n) = Expr opr <$> erase m <*> erase n
erase (If b m n) = If <$> erase b <*> erase m <*> erase n
erase (Fix bnd) = return $ Fix bnd -- unreachable
erase (Dor l u bnd) = return $ Dor l u bnd -- unreachable
erase (Print s) = return $ Print s
erase tm = throwError $ "erase: do not support " ++ show tm

eraseCase :: CasePatClause -> Contextual CasePatClause
eraseCase (p, cls) = (p,) <$> erasec cls

eraseCases :: CasePatClauses -> Contextual CasePatClauses
eraseCases = mapM eraseCase

eraseHandler :: HandlerClauses -> Contextual HandlerClauses
eraseHandler = mapM (\(l, cls) -> (l,) <$> eraseCase cls)

eraseCtx :: Context -> Contextual Context
eraseCtx Nil = return Nil
eraseCtx (ctx :< TmVar x ty (Just tm)) = do
  tm' <- erase tm
  ctx' <- eraseCtx ctx
  return $ ctx' :< TmVar x ty (Just tm')
eraseCtx (ctx :< _) = eraseCtx ctx

erasec :: CaseCls -> Contextual CaseCls
erasec (CaseTerm m) = CaseTerm <$> erase m
erasec (CaseBind bnd) = do
  (x, cls) <- unbind bnd
  cls' <- erasec cls
  return $ CaseBind (bind x cls')

evalCtx :: Context -> Runtime (Context, [(String, Term)])
evalCtx Nil = return (Nil, [])
evalCtx (ctx :< TmVar x ty (Just tm)) = do
  (ctx', results) <- evalCtx ctx
  put ctx'
  res <- eval tm
  return (ctx' :< TmVar x ty (Just res), results ++ [(name2String x, res)])
evalCtx (ctx :< _) = evalCtx ctx

-- * Evaluation

findGlobalTm :: Name Term -> Contextual Term
findGlobalTm x = get >>= help
  where
    help :: Context -> Contextual Term
    help Nil                                = throwError $ "Term var " ++ show x ++ " not found."
    help (_ :< TmVar y _ (Just m)) | x == y = return m
    help (_ :< TmVar y _ Nothing)  | x == y = throwError $ "Term var " ++ show x ++ " not defined."
    help (ctx :< _)                         = help ctx

getRet :: HandlerClauses -> Runtime CasePatClause
getRet = return . snd . last

getOpCls :: HandlerClauses -> Label -> Runtime CasePatClause
getOpCls clss l = case find ((== l) . fst) clss of
  Nothing -> throwError $ "handler clause for label " ++ l ++ " not found."
  Just (_, cls) -> return cls

underBnd :: Bind (Name Term) Term -> (Term -> Term) -> Runtime (Bind (Name Term) Term)
underBnd bnd f = do
  (x, m) <- unbind bnd
  return $ bind x (f m)

eval :: Term -> Runtime Term
eval (Var x) = lift $ findGlobalTm x
eval (App m n) = do
  m' <- eval m
  case m' of
    Dor op u cont -> Dor op u <$> underBnd cont (`App` n)
    Lam bnd -> do
      n' <- eval n
      case n' of
        Dor op u cont -> Dor op u <$> underBnd cont (m' `App`)
        _ -> do
          (x, body) <- unbind bnd
          eval $ subst x n' body
    LamCase cls -> do -- deal with partial application
      n' <- eval n
      case n' of
        Dor op u cont -> Dor op u <$> underBnd cont (m' `App`)
        _ -> evalCasePartial [] [n'] [cls] False >>= \case
          Left [cls'] -> return $ LamCase cls'
          Left _      -> throwError "impossible"
          Right tm  -> eval tm
    _ -> throwError "eval: App stuck."
eval (Let m bnd) = do
  m' <- eval m
  case m' of
    Dor op u cont -> Dor op u <$> underBnd cont (`Let` bnd)
    _ -> do
      (x, n) <- unbind bnd
      eval $ subst x m' n
eval (LetRec _ bnd) = do
  (x, (m, n)) <- unbind bnd -- m should be a value (lambda)
  let fm = Fix $ bind x m
  eval $ subst x fm n
eval (Fix bnd) = do
  (x, m) <- unbind bnd
  eval $ subst x (Fix bnd) m
eval (Do op m) = eval m >>= \case
  Dor op' u cont -> Dor op' u <$> underBnd cont (Do op)
  m' -> return $ Dor (op, 0) m' (tmb "x" (var "x"))
eval (Dor op m bnd) = do
  -- m' <- eval m   -- m should actually always be a value
  return $ Dor op m bnd
eval (Mask e m) = do
  m' <- eval m
  case m' of
    Dor (op, level) u cont -> return $ Dor (op, level + countEff op e) u cont
    _ -> return m'
eval (Handle _ m h) = do
  m' <- eval m
  let e = getOps h
  case m' of
    u | isVal u -> getRet h >>= \ cls -> evalCase [] [u] [cls] >>= eval
    Dor (op, level) u cont | countEff op e > 0 && level == 0 -> getOpCls h op >>= \ cls -> do
        (y, cont') <- unbind cont
        res <- evalCase [] [u, Lam (bind y $ Handle Nothing cont' h)] [cls]
        eval res
    Dor (op, level) u cont | countEff op e > 0 && level > 0 ->
      Dor (op, level - 1) u <$> underBnd cont (\x -> Handle Nothing x h)
    Dor (op, level) u cont | countEff op e == 0 ->
      Dor (op, level) u <$> underBnd cont (\x -> Handle Nothing x h)
    _ -> throwError $ "eval: Handle stuck for " ++ show m'
--
eval (If b m n) = eval b >>= \case
  Dor op u cont   -> Dor op u <$> underBnd cont (\b' -> If b' m n)
  Cons "true" []  -> eval m
  Cons "false" [] -> eval n
  _ -> throwError "eval: If stuck."
eval (Expr opr m n) = do
  m' <- eval m
  case m' of
    Dor op u cont -> Dor op u <$> underBnd cont (flip (Expr opr) n)
    TmInt m1 -> do
      n' <- eval n
      case n' of
        Dor op u cont -> Dor op u <$> underBnd cont (Expr opr m' )
        TmInt n1 -> if isCalc opr then do
            res <- calc opr m1 n1
            return . TmInt $ res
          else do
            res <- comp opr m1 n1
            return $ if res then tmTrue else tmFalse
        _ -> throwError "eval: Expr stuck."
    _ -> throwError "eval: Expr stuck."
  where
    calc :: String -> Int -> Int -> Runtime Int
    calc "+" x y = return $ x + y
    calc "-" x y = return $ x - y
    calc  _ _ _ = throwError "eval: Unknown operator."
    comp :: String -> Int -> Int -> Runtime Bool
    comp "==" x y = return $ x == y
    comp "/=" x y = return $ x /= y
    comp "<=" x y = return $ x <= y
    comp ">=" x y = return $ x >= y
    comp ">"  x y = return $ x > y
    comp "<"  x y = return $ x < y
    comp  _ _ _ = throwError "eval: Unknown operator."
eval (Cons l ms) = evalCons l [] ms
eval (CasePat ms casecls) = do
  ms' <- mapM eval ms
  res <- evalCase [] ms' casecls
  eval res
eval (Print s) = tell s >> return tmUnit
eval v | isVal v = return v -- needs to be after the empty casepat case (which is also a value)
eval _ = undefined

evalCons :: Label -> [Term] -> [Term] -> Runtime Term
evalCons l ns [] = return $ Cons l ns
evalCons l ns (m:ms) = do
  m' <- eval m
  case m' of
    Dor op u cont -> Dor op u <$> underBnd cont (\x -> Cons l (ns ++ [x] ++ ms))
    _ -> evalCons l (ns ++ [m']) ms

evalCase :: [Term] -> [Term] -> CasePatClauses -> Runtime Term
evalCase ns [] [] = throwError $ "evalCase: No matching clause for " ++ show ns
evalCase ns [] ((pats, cls):casecls) = matchMany ns pats cls >>= \case
  Just ([], CaseTerm m) -> return m
  Just _  -> throwError "evalCase: Binders left."
  Nothing -> evalCase ns [] casecls
evalCase ns (m:ms) casecls = do
  m' <- eval m
  case m' of
    Dor op u cont -> Dor op u <$> underBnd cont (\x -> CasePat (ns ++ [x] ++ ms) casecls)
    _ -> evalCase (ns ++ [m']) ms casecls


-- | First evaluate the second argument to the first argument. Then
-- try to find a matching clause for the first argument. The bool
-- documents whether pattern-matching succeeded before.
evalCasePartial :: [Term] -> [Term] -> CasePatClauses -> Bool -> Runtime (Either CasePatClauses Term)
evalCasePartial ns [] [] False = throwError $ "evalCase: No matching clause for " ++ show ns
evalCasePartial _  [] [] True = return $ Left []
evalCasePartial ns [] ((pats, cls):casecls) b = do
  matchMany ns pats cls >>= \case
    Just ([], CaseTerm m) -> return $ Right m
    Just (pats', cls') -> evalCasePartial ns [] casecls True >>= \case
      Left casecls' -> return . Left $ (pats', cls') : casecls'
      Right _ -> throwError "evalCase: The number of terms should either match \
        \the number of patterns for all clauses or not."
    Nothing -> evalCasePartial ns [] casecls b
evalCasePartial ns (m:ms) casecls b = do
  m' <- eval m
  case m' of
    Dor op u cont -> Right . Dor op u <$> underBnd cont (\x -> CasePat (ns ++ [x] ++ ms) casecls)
    _ -> evalCasePartial (ns ++ [m']) ms casecls b

-- | Try to match terms with patterns one by one. Allow leaving complete patterns.
matchMany :: [Term] -> [Pattern] -> CaseCls -> Runtime (Maybe ([Pattern], CaseCls))
matchMany []     ps     cls = return . Just $ (ps, cls)
matchMany (m:ms) (p:ps) cls = matchSingle m p cls >>= \case
  Just cls' -> matchMany ms ps cls'
  Nothing -> return Nothing
matchMany _ _ _ = return Nothing

-- | Try to match one term with one pattern. Succeed if fully match.
matchSingle :: Term -> Pattern -> CaseCls -> Runtime (Maybe CaseCls)
matchSingle m PVar (CaseBind bnd) = do
  (x, cls) <- unbind bnd
  return . Just $ subst x m cls
matchSingle (TmInt n) (PInt n') cls | n == n' = return . Just $ cls
matchSingle (TmChar c) (PChar c') cls | c == c' = return . Just $ cls
matchSingle (Cons l ms) (PCons l' ps) cls | equalCons l l' = matchMany ms ps cls >>= \case
  Just ([], cls') -> return . Just $ cls'
  _ -> return Nothing
matchSingle _ _ _ = return Nothing