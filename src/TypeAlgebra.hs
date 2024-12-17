module TypeAlgebra
  ( module TypeAlgebra.Algebra,
    algebraCost,
    ruleCost,
    searchPathCost,
    algebraSearch,
    algebraSolutions,
    algebraCardinality,
  )
where

import Control.Lens.Plated (Plated, rewriteM)
import Control.Monad ((>=>))
import Control.Monad.Trans.State (execState, modify)
import Data.Foldable (toList)
import Data.Functor (($>))
import Data.List (sortBy)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NEL
import Data.Maybe (listToMaybe)
import Data.Monoid (Sum)
import Data.Ord (comparing)
import qualified Data.Set as Set
import TypeAlgebra.Algebra (Algebra (..), Cardinality (..), Variance (..), subst, variance)
import TypeAlgebra.Rules (RewriteLabel (RewriteCommutative), Rule, rules, runRulePlated)

-- Disincentivise quantification and functions.
algebraCost ::
  Algebra x ->
  Sum Int
algebraCost =
  flip execState 0 . rewriteM (\a -> modify (+ f a) $> Nothing)
  where
    f (Forall _ _) =
      20
    f (Exponent _ _) =
      10
    f _ =
      5

-- Disincentivise commutative since it's very commonly applicable but not so useful.
ruleCost ::
  RewriteLabel ->
  Sum Int
ruleCost RewriteCommutative =
  30
ruleCost _ =
  1

searchPathCost ::
  NonEmpty (RewriteLabel, Algebra x) ->
  Sum Int
searchPathCost xs =
  foldMap ruleCost (fst <$> xs) <> algebraCost (snd (NEL.head xs))

-- | Finds a solution by applying weighted rewrite rules.
-- | Doesn't search from the same element twice.
-- | Found element is returned with the successful path that the search took to get there.
algebraSearch ::
  (Plated a, Foldable f, Foldable g, Ord a, Ord c) =>
  f (l, Rule g a) ->
  (NonEmpty (l, a) -> c) ->
  a ->
  [NonEmpty (l, a)]
algebraSearch rs cost query =
  go (Set.singleton query) (runRules query [])
  where
    go seen ((_, a) : as) =
      let (_, h) =
            NEL.head a
          a' =
            runRules h (toList a)
          seen' =
            Set.insert h seen
       in if null a'
            then a : go seen' as
            else
              if Set.member h seen
                then a : go seen as
                else go seen' (sortBy (comparing fst) (a' <> as))
    go _ [] =
      []
    runRules h t =
      (\a -> (cost a, a)) <$> foldMap (run h t) (toList rs)
    run h t (l, r) =
      (\a' -> (l, a') :| t) <$> runRulePlated r h

algebraSolutions ::
  Ord x =>
  Algebra x ->
  [NEL.NonEmpty (RewriteLabel, Algebra x)]
algebraSolutions =
  filter
    ( \xs ->
        ( case NEL.head xs of
            (_, Cardinality _) -> True
            _ -> False
        )
    )
    . algebraSearch rules searchPathCost

algebraCardinality ::
  Ord x =>
  Algebra x ->
  Maybe Cardinality
algebraCardinality (Cardinality c) =
  Just c
algebraCardinality a =
  listToMaybe (algebraSolutions a) >>= f . snd . NEL.head
  where
    f (Cardinality n) =
      Just n
    f _ =
      Nothing
