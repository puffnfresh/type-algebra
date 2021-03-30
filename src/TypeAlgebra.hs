{-# LANGUAGE TupleSections #-}

module TypeAlgebra
  ( Rule (..),
    runRule,
    runRulePlated,
    buildRewriteForest,
    forestPaths,
    Algebra (..),
    (->>),
    subst,
    Variance (..),
    variance,
    algebraSolutions,
    algebraArity,
    RewriteLabel (..),
    rules,
    arithmetic,
    curryProduct,
    currySum,
    associative,
    commutative,
    distributive,
    yonedaCovariant,
    yonedaContravariant,
    introduceArity,
    removeForall,
    prettySolution,
    prettyPrec,
  )
where

import Control.Applicative (Applicative (liftA2), (<|>))
import Control.Lens.Plated (Plated (plate), transformM)
import Control.Monad ((>=>))
import Control.Monad.Trans.Writer (WriterT (WriterT, runWriterT))
import Control.Monad.Zip (mzip)
import Data.Foldable (asum, toList)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NEL
import qualified Data.Map as M
import Data.Maybe (listToMaybe)
import Data.Monoid (Sum)
import Data.Tree (Tree (Node, rootLabel, subForest))

newtype Rule f a
  = Rule (a -> f a)

runRule :: Rule f a -> a -> f a
runRule (Rule f) =
  f

runRulePlated :: (Plated a, Foldable f) => Rule f a -> a -> [a]
runRulePlated (Rule f) =
  asum . fmap filterIdentity . runWriterT . transformM go
  where
    filterIdentity (a, b) =
      [a | b == (1 :: Sum Int)]
    go a =
      let as =
            f a
          as' =
            fmap (,1) (toList as)
       in WriterT ((a, 0 :: Sum Int) : as')

buildRewriteForest :: (Plated a, Foldable f, Foldable g) => f (l, Rule g a) -> a -> [Tree (l, a)]
buildRewriteForest rules =
  forest
  where
    forest a =
      foldMap (\(l, r) -> foldMap (\b -> [Node (l, b) (forest b)]) (runRulePlated r a)) rules

-- | Breadth-first collecting of nodes, with their paths.
forestPaths :: [Tree a] -> [NonEmpty a]
forestPaths =
  go []
  where
    go path ts =
      foldMap (parent path) ts <> foldMap (children path) ts
    parent path =
      (: []) . flip (:|) path . rootLabel
    children parentPath node =
      go (rootLabel node : parentPath) (subForest node)

algebraSolutions :: Ord x => Algebra x -> [NEL.NonEmpty (RewriteLabel, Algebra x)]
algebraSolutions =
  filter
    ( \xs ->
        ( case NEL.head xs of
            (_, Arity _) -> True
            _ -> False
        )
    )
    . forestPaths
    . buildRewriteForest rules

algebraArity :: Ord x => Algebra x -> Maybe Int
algebraArity =
  listToMaybe . algebraSolutions >=> f . snd . NEL.head
  where
    f (Arity n) =
      Just n
    f _ =
      Nothing

instance Plated (Algebra e) where
  plate _ (Arity a) =
    pure (Arity a)
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

-- | Polynomials, without subtraction, with explicit quantification.
data Algebra x
  = Arity Int
  | Sum (Algebra x) (Algebra x)
  | Product (Algebra x) (Algebra x)
  | Exponent (Algebra x) (Algebra x)
  | Var x
  | Forall x (Algebra x)
  deriving (Eq, Ord, Show)

instance Functor Algebra where
  fmap _ (Arity n) =
    Arity n
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
subst _ _ (Arity n) =
  Arity n
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
variance (Arity _) =
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

data RewriteLabel
  = RewriteArithmetic
  | RewriteCurrySum
  | RewriteCurryProduct
  | RewriteAssociative
  | RewriteCommutative
  | RewriteDistributive
  | RewriteYonedaCovariant
  | RewriteYonedaContravariant
  | RewriteIntroduceArity
  | RewriteRemoveForall
  deriving (Eq, Ord, Show)

rules :: Ord x => [(RewriteLabel, Rule Maybe (Algebra x))]
rules =
  [ (RewriteIntroduceArity, Rule introduceArity),
    (RewriteYonedaCovariant, Rule yonedaCovariant),
    (RewriteYonedaContravariant, Rule yonedaContravariant),
    (RewriteRemoveForall, Rule removeForall),
    (RewriteArithmetic, Rule arithmetic),
    (RewriteCurrySum, Rule currySum),
    (RewriteCurryProduct, Rule curryProduct),
    (RewriteAssociative, Rule associative),
    (RewriteDistributive, Rule distributive),
    (RewriteCommutative, Rule commutative)
  ]

arithmetic ::
  Algebra x ->
  Maybe (Algebra y)
arithmetic (Exponent (Arity a) (Arity b)) =
  Just (Arity (a ^ b))
arithmetic (Product (Arity a) (Arity b)) =
  Just (Arity (a * b))
arithmetic (Sum (Arity a) (Arity b)) =
  Just (Arity (a + b))
arithmetic _ =
  Nothing

-- | forall x. (a -> x) -> f x ~ f a
yonedaCovariant ::
  Ord x =>
  Algebra x ->
  Maybe (Algebra x)
yonedaCovariant (Exponent fx (Exponent (Var x) a)) =
  yoneda fx a x Covariant
yonedaCovariant _ =
  Nothing

-- | forall x. (x -> a) -> f x ~ f a
yonedaContravariant ::
  Ord x =>
  Algebra x ->
  Maybe (Algebra x)
yonedaContravariant (Exponent fx (Exponent a (Var x))) =
  yoneda fx a x Contravariant
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
associative _ =
  Nothing

-- | (Either a b, c) ~ Either (a, c) (b, c)
-- | (a, Either b c) ~ Either (a, b) (a, c)
-- | Either a b -> c ~ (a -> c, b -> c)
-- | a -> (b, c) ~ (a -> b, a -> c)
distributive ::
  Algebra x ->
  Maybe (Algebra x)
distributive (Product (Sum a b) c) =
  Just (Sum (Product a c) (Product b c))
distributive (Product a (Sum b c)) =
  Just (Sum (Product a b) (Product a c))
distributive (Exponent a (Sum b c)) =
  Just (Product (Exponent a b) (Exponent a c))
distributive (Exponent (Product a b) c) =
  Just (Product (Exponent a c) (Exponent b c))
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

-- | Either a b -> c ~ (a -> c, b -> c)
currySum ::
  Algebra x ->
  Maybe (Algebra x)
currySum (Exponent c (Sum a b)) =
  Just (Product (Exponent c a) (Exponent c b))
currySum _ =
  Nothing

-- | (a * a) -> b ~ (2 -> a) -> b
-- | a -> b ~ (1 -> a) -> b
introduceArity ::
  Eq x =>
  Algebra x ->
  Maybe (Algebra x)
introduceArity (Exponent c (Product (Var a) (Var b))) =
  if a == b
    then Just (Exponent c (Exponent (Var a) (Arity 2)))
    else Nothing
introduceArity (Exponent b (Var a)) =
  Just (Exponent b (Exponent (Var a) (Arity 1)))
introduceArity _ =
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

prettySolution :: Algebra String -> NEL.NonEmpty (RewriteLabel, Algebra String) -> String
prettySolution x xs =
  unlines
    (prettyPrec 0 x "" : reverse (toList (fmap f xs)))
  where
    f (t, a) =
      "= " <> prettyPrec 0 a ("\t-- via " <> l t)
    l RewriteArithmetic =
      "arithmetic"
    l RewriteAssociative =
      "associative"
    l RewriteCommutative =
      "commutative"
    l RewriteCurryProduct =
      "curry product"
    l RewriteCurrySum =
      "curry sum"
    l RewriteYonedaContravariant =
      "contravariant yoneda lemma"
    l RewriteYonedaCovariant =
      "covariant yoneda lemma"
    l RewriteDistributive =
      "distributive"
    l RewriteIntroduceArity =
      "introduce arity"
    l RewriteRemoveForall =
      "remove forall"

prettyPrec ::
  Int ->
  Algebra String ->
  ShowS
prettyPrec _ (Arity n) =
  shows n
prettyPrec p (Sum a b) =
  showParen (p > 2) (prettyPrec 2 a . showString " + " . prettyPrec 2 b)
prettyPrec p (Product a b) =
  showParen (p > 3) (prettyPrec 3 a . showString " * " . prettyPrec 3 b)
prettyPrec p (Exponent a b) =
  -- showParen (p >= 4) (prettyPrec 4 a . showString " ^ " . prettyPrec 4 b)
  showParen (p >= 4) (prettyPrec 4 b . showString " -> " . prettyPrec 4 a)
prettyPrec _ (Var x) =
  showString x
prettyPrec p (Forall x a) =
  showParen (p > 1) (showString "∀ " . showString x . showString ". " . prettyPrec 1 a)
