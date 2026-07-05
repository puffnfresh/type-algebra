module TypeAlgebra.Rules
  ( Rule (..),
    runRulePlated,
    RewriteLabel (..),
    rules,
  )
where

import Control.Comonad.Store (experiment)
import Control.Lens (Plated, contexts)
import Control.Monad ((>=>))
import Data.Foldable (Foldable (toList))
import TypeAlgebra.Algebra (Algebra)
import TypeAlgebra.Rewrites
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

newtype Rule f a
  = Rule (a -> f a)

runRulePlated ::
  (Plated a, Foldable f) =>
  Rule f a ->
  a ->
  [a]
runRulePlated (Rule f) =
  contexts >=> experiment (toList . f)

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
  | RewriteIntroduceCardinality
  | RewriteMoveForall
  | RewriteRemoveForall
  deriving (Eq, Ord, Show)

rules ::
  Ord x =>
  [(RewriteLabel, Rule [] (Algebra x))]
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
    (RewriteIntroduceCardinality, Rule introduceCardinality)
  ]
  where
    rule f =
      Rule (toList . f)
