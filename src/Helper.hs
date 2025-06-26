module Helper (module Helper) where

import Unbound.Generics.LocallyNameless
import Syntax

-- constructors for types

eff :: Row -> Effect
eff = row2eff

forallty :: String -> Kind -> Type -> Type
forallty alpha k a = All k (bind (s2n alpha) a)

tabs :: String -> Kind -> Term -> Term
tabs alpha k a = TAbs k (bind (s2n alpha) a)

abs :: Row -> Type -> Type
abs ops = Mod (Abs (eff ops))

aex :: Row -> Type -> Type
aex ops = Mod (Rel En (eff ops))

tvar :: String -> Type
tvar = TVar . s2n

-- constructors for terms

int :: Int -> Term
int = TmInt

unit :: Term
unit = tmUnit

var :: String -> Term
var x = Var (s2n x)

tmb :: String -> Term -> Bind (Name Term) Term
tmb x = bind (s2n x)

tyb :: String -> Type -> Bind (Name Type) Type
tyb x = bind (s2n x)

lam :: String -> Term -> Term
lam x m = Lam (bind (s2n x) m)

-- lamA :: String -> Type -> Term -> Term
-- lamA x a m = LamAnno a (bind (s2n x) m)

anno :: Term -> Type -> Term
anno = Anno

letIn :: String -> Term -> Term -> Term
letIn x m n = Let m (bind (s2n x) n)

seq :: Term -> Term -> Term
seq m n = Let m (bind (s2n "_") n)

letAnno :: String -> Type -> Term -> Term -> Term
letAnno x a m n = Let (Anno m a) (bind (s2n x) n)

letRec :: String -> Type -> Term -> Term -> Term
letRec x a m n = LetRec a (bind (s2n x) (m, n))

mask :: [Label] -> Term -> Term
mask l = Mask (eff $ map (`Eff` []) l)

-- ret :: String -> Term -> Handler
-- ret x m = Return (bind (s2n x) m)

-- cls :: Label -> String -> String -> Term -> Handler -> Handler
-- cls l p r m = Op l (bind (s2n p) (bind (s2n r) m))

pvar :: Pattern
pvar = PVar

pat :: Label -> [Pattern] -> Pattern
pat = PCons

cbind :: [String] -> Term -> CaseCls
cbind xs m = foldr (\ x t -> CaseBind . bind (s2n x) $ t) (CaseTerm m) xs
