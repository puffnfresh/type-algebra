module TypeAlgebra.Rewrites
  ( arithmetic,
    associative,
    commutative,
    curryProduct,
    currySum,
    distributive,
    introduceCardinality,
    moveForall,
    removeForall,
    uncurryProduct,
    yonedaContravariant,
    yonedaCovariant,
  )
where

import Control.Applicative ((<|>))
import Control.Monad.Zip (mzip)
import qualified Data.Map as M
import TypeAlgebra.Algebra (Algebra (..), Cardinality (..), Variance (..), subst, variance)

arithmetic ::
  Algebra x ->
  Maybe (Algebra x)
arithmetic (Sum a (Cardinality Infinite)) =
  Just (Cardinality Infinite)
arithmetic (Sum (Cardinality Infinite) a) =
  Just (Cardinality Infinite)
arithmetic (Sum a (Cardinality (Finite  0))) =
  Just a
arithmetic (Sum (Cardinality (Finite 0)) a) =
  Just a
arithmetic (Product (Cardinality (Finite 0)) _) =
  Just (Cardinality (Finite 0))
arithmetic (Product _ (Cardinality (Finite 0))) =
  Just (Cardinality (Finite 0))
arithmetic (Product a (Cardinality (Finite 1))) =
  Just a
arithmetic (Product (Cardinality (Finite 1)) a) =
  Just a
arithmetic (Product _ (Cardinality Infinite)) =
  Just (Cardinality Infinite)
arithmetic (Product (Cardinality Infinite) _) =
  Just (Cardinality Infinite)
arithmetic (Exponent _ (Cardinality (Finite 0))) =
  Just (Cardinality (Finite 1))
arithmetic (Exponent a (Cardinality (Finite 1))) =
  Just a
arithmetic (Exponent (Cardinality Infinite) _) =
  Just (Cardinality Infinite)
arithmetic (Exponent _ (Cardinality Infinite)) =
  Just (Cardinality Infinite)
arithmetic (Exponent (Cardinality (Finite a)) (Cardinality (Finite b))) =
  Just (Cardinality (Finite (a ^ b)))
arithmetic (Product (Cardinality (Finite a)) (Cardinality (Finite b))) =
  Just (Cardinality (Finite (a * b)))
arithmetic (Sum (Cardinality (Finite a)) (Cardinality (Finite b))) =
  Just (Cardinality (Finite (a + b)))
arithmetic _ =
  Nothing

-- | forall x. (a -> x) -> f x ~ f a
yonedaCovariant ::
  Ord x =>
  Algebra x ->
  Maybe (Algebra x)
yonedaCovariant (Forall x (Exponent fx (Exponent (Var y) a))) =
  if x == y then yoneda fx a x Covariant else Nothing
yonedaCovariant _ =
  Nothing

-- | forall x. (x -> a) -> f x ~ f a
yonedaContravariant ::
  Ord x =>
  Algebra x ->
  Maybe (Algebra x)
yonedaContravariant (Forall x (Exponent fx (Exponent a (Var y)))) =
  if x == y then yoneda fx a x Contravariant else Nothing
yonedaContravariant _ =
  Nothing

yoneda ::
  Ord a =>
  Algebra a ->
  Algebra a ->
  a ->
  Variance ->
  Maybe (Algebra a)
yoneda fx a x v =
  if all (== (v, v)) (sameVariance fx a x)
    then Just (subst x a fx)
    else Nothing

sameVariance ::
  Ord x =>
  Algebra x ->
  Algebra x ->
  x ->
  Maybe (Variance, Variance)
sameVariance a b x =
  mzip (va <|> vb) (vb <|> va)
  where
    v =
      M.lookup x . variance
    va =
      v a
    vb =
      v b

-- | (a, b) ~ (b, a)
-- | Either a b ~ Either b a
commutative ::
  Algebra x ->
  Maybe (Algebra x)
commutative (Product a b) =
  Just (Product b a)
commutative (Sum a b) =
  Just (Sum b a)
commutative _ =
  Nothing

-- | ((a, b), c) ~ (a, (b, c))
-- | Either (Either a b) c ~ Either a (Either b c)
associative ::
  Algebra x ->
  Maybe (Algebra x)
associative (Product (Product a b) c) =
  Just (Product a (Product b c))
associative (Sum (Sum a b) c) =
  Just (Sum a (Sum b c))
associative (Sum a (Sum b c)) =
  Just (Sum (Sum a b) c)
associative _ =
  Nothing

-- | (Either a b, c) ~ Either (a, c) (b, c)
-- | (a, Either b c) ~ Either (a, b) (a, c)
-- | Either a b -> c ~ (a -> c, b -> c)
-- | a -> (b, c) ~ (a -> b, a -> c)
distributive ::
  Algebra x ->
  Maybe (Algebra x)
distributive (Forall x (Product a b)) =
  Just (Product (Forall x a) (Forall x b))
distributive (Product (Sum a b) c) =
  Just (Sum (Product a c) (Product b c))
distributive (Product a (Sum b c)) =
  Just (Sum (Product a b) (Product a c))
distributive _ =
  Nothing

-- | (a, b) -> c ~ a -> b -> c
curryProduct ::
  Algebra x ->
  Maybe (Algebra x)
curryProduct (Exponent c (Product a b)) =
  Just (Exponent (Exponent c b) a)
curryProduct _ =
  Nothing

-- | a -> b -> c ~ (a, b) -> c
uncurryProduct ::
  Algebra x ->
  Maybe (Algebra x)
uncurryProduct (Exponent (Exponent c b) a) =
  Just (Exponent c (Product a b))
uncurryProduct _ =
  Nothing

-- | Either a b -> c ~ (a -> c, b -> c)
currySum ::
  Eq x =>
  Algebra x ->
  Maybe (Algebra x)
currySum (Exponent c (Sum a b)) =
  Just (Product (Exponent c a) (Exponent c b))
currySum _ =
  Nothing

-- | (a * a) -> b ~ (2 -> a) -> b
-- | a -> b ~ (1 -> a) -> b
-- | a -> b ~ (0 -> a) -> b
introduceCardinality ::
  Eq x =>
  Algebra x ->
  [Algebra x]
introduceCardinality (Exponent c (Product (Var a) (Var b))) =
  [ Exponent c (Exponent (Var a) (Cardinality (Finite 2))) | a == b
  ]
introduceCardinality (Exponent b (Var a)) =
  [ Exponent b (Exponent (Var a) (Cardinality (Finite 1)))
  ]
introduceCardinality (Forall _ (Exponent _ (Exponent (Cardinality (Finite 1)) _))) =
  []
introduceCardinality (Forall _ (Exponent _ (Exponent _ (Cardinality (Finite 0))))) =
  []
introduceCardinality (Forall x a) =
  [ Forall x (Exponent a (Exponent (Cardinality (Finite 1)) (Var x))),
    Forall x (Exponent a (Exponent (Var x) (Cardinality (Finite 0))))
  ]
introduceCardinality _ =
  []

moveForall ::
  Ord x =>
  Algebra x ->
  Maybe (Algebra x)
moveForall (Forall x (Exponent a b)) =
  if M.member x (variance b)
    then Nothing
    else Just (Exponent (Forall x a) b)
moveForall (Forall x (Forall y a)) =
  Just (Forall y (Forall x a))
moveForall _ =
  Nothing

removeForall ::
  Ord x =>
  Algebra x ->
  Maybe (Algebra x)
removeForall (Forall x a) =
  if M.member x (variance a)
    then Nothing
    else Just a
removeForall _ =
  Nothing
