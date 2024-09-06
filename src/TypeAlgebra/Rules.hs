{-# LANGUAGE TupleSections #-}

module TypeAlgebra.Rules
  ( Rule (..),
    runRulePlated,
    RewriteLabel (..),
    rules,
  )
where

import Control.Lens (Plated, transformM)
import Control.Monad.Trans.Writer (WriterT (WriterT, runWriterT))
import Data.Foldable (Foldable (toList), asum)
import Data.Monoid (Sum)
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
