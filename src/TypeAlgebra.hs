{-# LANGUAGE TupleSections #-}

module TypeAlgebra
  ( Rule (..),
    runRule,
    runRulePlated,
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
    mathjaxSolution,
    prettySolution,
    prettyPrec,
  )
where

import Control.Applicative (Applicative (liftA2), (<|>))
import Control.Lens.Plated (Plated (plate), rewriteM, transformM)
import Control.Monad ((>=>))
import Control.Monad.Trans.State (execState, modify)
import Control.Monad.Trans.Writer (WriterT (WriterT, runWriterT))
import Control.Monad.Zip (mzip)
import Data.Foldable (asum, toList)
import Data.Functor (($>))
import Data.List (intersperse, sortBy)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NEL
import qualified Data.Map as M
import Data.Maybe (listToMaybe)
import Data.Monoid (Sum)
import Data.Ord (comparing)
import qualified Data.Set as Set

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

algebraCost ::
  Algebra x ->
  Int
algebraCost =
  flip execState 0 . rewriteM (\a -> modify (+ f a) $> Nothing)
  where
    f (Forall _ _) =
      20
    f (Exponent _ _) =
      10
    f _ =
      5

pathCost ::
  NonEmpty (a, Algebra x) ->
  Int
pathCost xs =
  length xs + algebraCost (snd (NEL.head xs))

-- | Breadth-first collecting of nodes, with their paths.
forestPaths :: (Plated a, Foldable f, Foldable g, Ord a) => f (l, Rule g a) -> (NonEmpty (l, a) -> Int) -> a -> [NonEmpty (l, a)]
forestPaths rs cost query =
  go (Set.singleton query) (runRules query [])
  where
    go seen ((_, a) : as) =
      let (_, h) =
            NEL.head a
          a' =
            runRules h (toList a)
          seen' =
            Set.insert h seen
       in if Set.member h seen
            then go seen as
            else
              if null a'
                then a : go seen' as
                else go seen' (sortBy (comparing fst) (a' <> as))
    go _ [] =
      []
    runRules h t =
      (\a -> (cost a, a)) <$> foldMap (run h t) (toList rs)
    run h t (l, r) =
      (\a' -> (l, a') :| t) <$> runRulePlated r h

algebraSolutions :: Ord x => Algebra x -> [NEL.NonEmpty (RewriteLabel, Algebra x)]
algebraSolutions =
  filter
    ( \xs ->
        ( case NEL.head xs of
            (_, Arity _) -> True
            _ -> False
        )
    )
    . forestPaths rules pathCost

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
  | RewriteUncurryProduct
  | RewriteAssociative
  | RewriteCommutative
  | RewriteDistributive
  | RewriteYonedaCovariant
  | RewriteYonedaContravariant
  | RewriteIntroduceArity
  | RewriteMoveForall
  | RewriteRemoveForall
  deriving (Eq, Ord, Show)

rules :: Ord x => [(RewriteLabel, Rule [] (Algebra x))]
rules =
  [ (RewriteYonedaCovariant, rule yonedaCovariant),
    (RewriteYonedaContravariant, rule yonedaContravariant),
    (RewriteMoveForall, rule moveForall),
    (RewriteRemoveForall, rule removeForall),
    (RewriteArithmetic, rule arithmetic),
    (RewriteCurrySum, rule currySum),
    (RewriteCurryProduct, rule curryProduct),
    (RewriteUncurryProduct, rule uncurryProduct),
    (RewriteAssociative, rule associative),
    (RewriteDistributive, rule distributive),
    (RewriteCommutative, rule commutative),
    (RewriteIntroduceArity, Rule introduceArity)
  ]
  where
    rule f =
      Rule (toList . f)

arithmetic ::
  Algebra x ->
  Maybe (Algebra x)
arithmetic (Sum a (Arity 0)) =
  Just a
arithmetic (Sum (Arity 0) a) =
  Just a
arithmetic (Product (Arity 0) _) =
  Just (Arity 0)
arithmetic (Product _ (Arity 0)) =
  Just (Arity 0)
arithmetic (Product a (Arity 1)) =
  Just a
arithmetic (Product (Arity 1) a) =
  Just a
arithmetic (Exponent a (Arity 1)) =
  Just a
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
introduceArity ::
  Eq x =>
  Algebra x ->
  [Algebra x]
introduceArity (Exponent b (Var a)) =
  [ Exponent b (Exponent (Var a) (Arity 1))
  ]
introduceArity (Forall _ (Exponent _ (Exponent (Arity 1) _))) =
  []
introduceArity (Forall _ (Exponent _ (Exponent _ (Arity 0)))) =
  []
introduceArity (Forall x a) =
  [ Forall x (Exponent a (Exponent (Arity 1) (Var x))),
    Forall x (Exponent a (Exponent (Var x) (Arity 0)))
  ]
introduceArity _ =
  []

moveForall ::
  Ord x =>
  Algebra x ->
  Maybe (Algebra x)
moveForall (Forall x (Exponent a b)) =
  if M.member x (variance b)
    then Nothing
    else Just (Exponent (Forall x a) b)
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

rewriteLabel :: RewriteLabel -> String
rewriteLabel RewriteArithmetic =
  "arithmetic"
rewriteLabel RewriteAssociative =
  "associative"
rewriteLabel RewriteCommutative =
  "commutative"
rewriteLabel RewriteCurryProduct =
  "curry product"
rewriteLabel RewriteUncurryProduct =
  "uncurry product"
rewriteLabel RewriteCurrySum =
  "curry sum"
rewriteLabel RewriteYonedaContravariant =
  "contravariant yoneda lemma"
rewriteLabel RewriteYonedaCovariant =
  "covariant yoneda lemma"
rewriteLabel RewriteDistributive =
  "distributive"
rewriteLabel RewriteIntroduceArity =
  "introduce arity"
rewriteLabel RewriteMoveForall =
  "move forall"
rewriteLabel RewriteRemoveForall =
  "remove forall"

mathjaxSolution :: Algebra String -> NEL.NonEmpty (RewriteLabel, Algebra String) -> String
mathjaxSolution x xs =
  unlines
    ( "\\begin{align*}" :
      intersperse "\\\\" (prettyPrec' (0 :: Int) x (" " <> prettyJustified x') : fmap prettyJustified xs')
        <> [ "\\end{align*}"
           ]
    )
  where
    (x' :| xs') =
      NEL.reverse xs

    prettyPrec' _ (Arity n) =
      shows n
    prettyPrec' p (Sum a b) =
      showParen (p > 2) (prettyPrec' 2 a . showString " + " . prettyPrec' 2 b)
    prettyPrec' p (Product a b) =
      showParen (p > 3) (prettyPrec' 3 a . showString " * " . prettyPrec' 3 b)
    prettyPrec' p (Exponent a b) =
      showParen (p >= 4) (prettyPrec' 4 b . showString " \\rightarrow " . prettyPrec' 4 a)
    prettyPrec' _ (Var y) =
      showString y
    prettyPrec' p (Forall y a) =
      showParen (p > 1) (showString "\\forall " . showString y . showString ". " . prettyPrec' 1 a)

    prettyJustified (l, a) =
      "&= " <> prettyPrec' (0 :: Int) a (" && \\text{(" <> rewriteLabel l <> ")}")

prettySolution :: Algebra String -> NEL.NonEmpty (RewriteLabel, Algebra String) -> String
prettySolution x xs =
  unlines
    (prettyPrec 0 x "" : reverse (toList (fmap f xs)))
  where
    f (t, a) =
      "= " <> prettyPrec 0 a ("\t-- via " <> rewriteLabel t)

prettyPrec ::
  Int ->
  Algebra String ->
  ShowS
prettyPrec _ (Arity n) =
  shows n
prettyPrec p (Sum a b) =
  showParen (p > 3) (prettyPrec 3 a . showString " + " . prettyPrec 3 b)
prettyPrec p (Product a b) =
  showParen (p > 4) (prettyPrec 4 a . showString " * " . prettyPrec 4 b)
prettyPrec p (Exponent a b) =
  -- showParen (p >= 4) (prettyPrec 4 a . showString " ^ " . prettyPrec 4 b)
  showParen (p > 2) (prettyPrec 3 b . showString " -> " . prettyPrec 2 a)
prettyPrec _ (Var x) =
  showString x
prettyPrec p (Forall x a) =
  showParen (p > 1) (showString "∀ " . showString x . showString ". " . prettyPrec 1 a)
