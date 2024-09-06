module TypeAlgebra.Algebra
  ( Cardinality (..),
    Algebra (..),
    subst,
    (->>),
    Variance (..),
    variance,
  )
where

import Control.Applicative (liftA2)
import Control.Lens (Plated (plate))
import qualified Data.Map as M

data Cardinality
  = Infinite
  | Finite Word
  deriving (Eq, Ord, Show)

-- | Polynomials, without subtraction, with explicit quantification.
data Algebra x
  = Cardinality Cardinality
  | Sum (Algebra x) (Algebra x)
  | Product (Algebra x) (Algebra x)
  | Exponent (Algebra x) (Algebra x)
  | Var x
  | Forall x (Algebra x)
  deriving (Eq, Ord, Show)

instance Functor Algebra where
  fmap _ (Cardinality n) =
    Cardinality n
  fmap f (Sum a b) =
    Sum (fmap f a) (fmap f b)
  fmap f (Product a b) =
    Product (fmap f a) (fmap f b)
  fmap f (Exponent a b) =
    Exponent (fmap f a) (fmap f b)
  fmap f (Forall a b) =
    Forall (f a) (fmap f b)
  fmap f (Var a) =
    Var (f a)

instance Plated (Algebra e) where
  plate _ (Cardinality a) =
    pure (Cardinality a)
  plate f (Sum a b) =
    liftA2 Sum (f a) (f b)
  plate f (Product a b) =
    liftA2 Product (f a) (f b)
  plate f (Exponent a b) =
    liftA2 Exponent (f a) (f b)
  plate _ (Var a) =
    pure (Var a)
  plate f (Forall x a) =
    fmap (Forall x) (f a)

subst ::
  Eq a =>
  a ->
  Algebra a ->
  Algebra a ->
  Algebra a
subst x a (Var y) =
  if x == y
    then a
    else Var y
subst _ _ (Cardinality n) =
  Cardinality n
subst x a (Sum b c) =
  Sum (subst x a b) (subst x a c)
subst x a (Product b c) =
  Product (subst x a b) (subst x a c)
subst x a (Exponent b c) =
  Exponent (subst x a b) (subst x a c)
subst x a (Forall y b) =
  if x == y
    then Forall y b
    else Forall y (subst x a b)

infixr 9 ->>

(->>) ::
  Algebra x ->
  Algebra x ->
  Algebra x
(->>) =
  flip Exponent

data Variance
  = Covariant
  | Contravariant
  | Invariant
  deriving (Eq, Ord, Show)

instance Semigroup Variance where
  (<>) a b =
    if a /= b
      then Invariant
      else a

invertVariance ::
  Variance ->
  Variance
invertVariance Invariant =
  Invariant
invertVariance Covariant =
  Contravariant
invertVariance Contravariant =
  Covariant

variance ::
  Ord x =>
  Algebra x ->
  M.Map x Variance
variance (Cardinality _) =
  mempty
variance (Sum a b) =
  M.unionWith (<>) (variance a) (variance b)
variance (Product a b) =
  M.unionWith (<>) (variance a) (variance b)
variance (Exponent a b) =
  M.unionWith (<>) (variance a) (fmap invertVariance (variance b))
variance (Forall x a) =
  M.delete x (variance a)
variance (Var x) =
  M.singleton x Covariant
