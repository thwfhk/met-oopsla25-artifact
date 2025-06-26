{-# LANGUAGE DeriveTraversable, MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables, FlexibleContexts, UndecidableInstances, DeriveGeneric #-}

module BwdFwd (module BwdFwd) where

import Data.Foldable ()
import Data.Monoid ()
import Data.Traversable ()
import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)

data Bwd a = Nil | Bwd a :< a
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic)

infixl 5 :<

instance Semigroup (Bwd a) where
  xs <> Nil         = xs
  xs <> (ys :< y)  = (xs <> ys) :< y

instance Monoid (Bwd a) where
    mempty = Nil
    mappend = (<>)

singleBwd :: a -> Bwd a
singleBwd x = Nil :< x

(<><) :: Bwd a -> [a] -> Bwd a
xs <>< []       = xs
xs <>< (y : ys) = (xs :< y) <>< ys

infixl 4 <><

(<>>) :: Bwd a -> [a] -> [a]
Nil         <>> ys = ys
(xs :< x)  <>> ys = xs <>> (x : ys)

fwd :: Bwd a -> [a]
fwd = (<>> [])

bwd :: [a] -> Bwd a
bwd = (Nil <><)

lookupBwd :: Eq a => a -> Bwd (a, b) -> Maybe b
lookupBwd x xs = lookup x (fwd xs)

lengthBwd :: Bwd a -> Int
lengthBwd Nil = 0
lengthBwd (xs :< _) = succ (lengthBwd xs)

(<.>) :: Monoid m => m -> m -> m
(<.>) = mappend


instance Alpha a => Alpha (Bwd a)

instance Subst t a => Subst t (Bwd a)