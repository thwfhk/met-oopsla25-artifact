{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Printer (module Printer) where

import Syntax

import Prettyprinter
import Unbound.Generics.LocallyNameless
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad hiding (ap)
import Prelude hiding (all)

newtype Printful a = Printful (StateT Int (FreshMT Identity) a)
deriving instance Applicative Printful
deriving instance Functor Printful
deriving instance Monad Printful
deriving instance MonadState Int Printful
deriving instance Fresh Printful


showType :: Type -> String
showType = show . runPrintful . printType . removeTopEmpAbs

showEffect :: Effect -> String
showEffect e = case e of
  En -> "."
  _ -> show . runPrintful . printEffect $ e

showValue :: Term -> String
showValue = show . runPrintful . printValue

runPrintful :: Printful a -> a
runPrintful (Printful m) = fst . runIdentity . runFreshMT . flip runStateT 0 $ m

defaultStatus :: Integer
defaultStatus = 0

reset :: Printful ()
reset = put 0

isFunArg :: Printful Bool
isFunArg = gets (== 1)

inFunArg :: Printful ()
inFunArg = put 1

isDataArg :: Printful Bool
isDataArg = gets (== 2)

inDataArg :: Printful ()
inDataArg = put 2

inModalArg :: Printful ()
inModalArg = put 3

isArg :: Printful Bool
isArg = gets (>= 1)

isDataModalArg :: Printful Bool
isDataModalArg = gets (>= 2)

withStatus :: Printful () -> Printful a -> Printful a
withStatus f m = do
  f
  res <- m
  reset
  return res

paren :: Doc a -> Doc a
paren x = "(" <> x <> ")"

printKind :: Kind -> Doc a
printKind Pure = "Abs"
printKind Any  = "Any"
printKind EffectKind  = "Eff"

printBinder :: (Name Type, Kind) -> Doc a
printBinder (alpha, Any)  = pretty (name2String alpha)
printBinder (alpha, Pure) = "[" <> pretty (name2String alpha) <> "]"
printBinder (alpha, EffectKind)  =  "{" <> pretty (name2String alpha) <> "}"

printRow :: Row -> Printful (Doc a)
printRow row = do
  res <- mapM printEff row
  return . concatWith (<>) . zipWith (<>) ("" : repeat ", ") $ res

printEffect :: Effect -> Printful (Doc a)
printEffect = printRow . eff2row

printEff :: Eff -> Printful (Doc a)
printEff (Eff name args) = do
  argsp <- mapM printType args
  case argsp of
    [] -> return $ pretty name
    _  -> return $ pretty name <+> hsep argsp

removeTopEmpAbs :: Type -> Type
removeTopEmpAbs (Mod (Abs En) a) = a
removeTopEmpAbs a = a

printType :: Type -> Printful (Doc a)
printType (TVar v) = return $ pretty (name2String v)
printType (a `Arr` b) = do
  isp <- isArg
  reset
  ap <- withStatus inFunArg $ printType a
  bp <- printType b
  let res = ap <+> "->" <+> bp
  return $ if isp then paren res else res
printType all@All{} = do
  isp <- isArg
  reset
  (aks, body) <- unbindAll all
  ap <- printType body
  let res = "forall" <+>
            foldr (\(a, k) b -> printBinder (a, k) <+> b)
                  ("." <+> ap) aks
  return $ if isp then paren res else res
printType (Mod mu a) = do
  mup <- printType mu
  ap <- withStatus inModalArg $ printType a
  return $ mup <> ap
printType (Abs e) = do
  ep <- printEffect e
  return $ "[" <> ep <> "]"
printType (Rel l d) = do
  lp <- printEffect l
  dp <- printEffect d
  let res = if l == En then "<" <> dp <> ">"
            else "<" <> lp <> "|" <> dp <> ">"
  return res
printType (ADT name args) = do
  isp <- isDataModalArg
  reset
  argsp <- mapM (withStatus inDataArg . printType) args
  let res = case name of
        "Unit" -> "1"
        "Pair" ->  parens $ head argsp <> " * " <> argsp !! 1
        "List" | show (head argsp) == "Char" -> "String"
        _      -> if null argsp then pretty name
                  else (if isp then paren else id) $ pretty name <+> hsep argsp
  return res
-- printType TUnit = return "1"
-- printType TBool = return "Bool"
printType TInt     = return "Int"
printType TChar    = return "Char"
printType ty       = error $ "printType: do not support " ++ show ty
-- printType (TPair a b) = do
--   ap <- printType a
--   bp <- printType b
--   return $ "(" <> ap <> ", " <> bp <> ")"

unbindAll :: Type -> Printful ([(Name Type, Kind)], Type)
unbindAll (All k bnd) = do
  (alpha, body) <- unbind bnd
  (aks, res) <- unbindAll body
  return ((alpha, k) : aks, res)
unbindAll ty = return ([], ty)

printValue :: Term -> Printful (Doc a)
printValue (Var v) = return $ pretty (name2String v)
printValue Lam{} = return "<fun>"
printValue LamCase{} = return "<fun>"
-- printValue Unit = return "()" 
-- printValue TmTrue = return "true"
-- printValue TmFalse = return "false"
printValue (TmInt n)  = return $ pretty n
printValue (TmChar c) = return $ pretty c
printValue (Cons name args) = do
  isp <- isDataModalArg
  reset
  argsp <- mapM (withStatus inDataArg . printValue) args
  let res = case name of
        "unit" -> "()"
        "pair" ->  paren $ head argsp <> ", " <> argsp !! 1
        "nil"  -> "[]"
        "nils" -> "\"\""
        "cons" -> case head args of
          TmChar{} -> concatString (head argsp) (argsp !! 1)
          _        -> concatList (head argsp) (argsp !! 1)
        _      -> if null argsp then pretty name else pretty name <+> hsep argsp
  return $ if isp && not (null argsp) && name /= "pair" && name /= "cons" then paren res else res
printValue _ = return "Not a result value."

concatString :: Doc a -> Doc a -> Doc a
concatString x xs =
  let s = show x
  in let ss = show xs
  in let res = "\"" ++ s ++ if ss == "\"\"" then "\"" else drop 1 ss
  in pretty res

concatList :: Doc a -> Doc a -> Doc a
concatList x xs =
  let s = show x
  in let ss = show xs
  in let res = "[" ++ s ++ if ss == "[]" then "]" else ", " ++ drop 1 ss
  in pretty res