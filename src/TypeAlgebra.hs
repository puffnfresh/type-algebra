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

import Control.Lens.Plated (Plated, rewrite, rewriteM)
import Control.Monad.Trans.State (execState, modify)
import Data.Foldable (toList)
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NEL
import qualified Data.Map as M
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Monoid (Sum)
import qualified Data.Set as Set
import TypeAlgebra.Algebra (Algebra (..), Cardinality (..), Variance (..), subst, variance)
import TypeAlgebra.Rules (RewriteLabel (RewriteArithmetic, RewriteCommutative, RewriteIntroduceCardinality), Rule (..), rules, runRulePlated)
import TypeAlgebra.Rewrites (arithmetic)

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
  go (Set.singleton query) (enqueue M.empty (runRules query []))
  where
    go seen frontier =
      maybe [] (go' seen) (M.minViewWithKey frontier)
    go' seen ((_, []), frontier') =
      go seen frontier'
    go' seen ((c, a : rest), frontier') =
      let
        frontier'' =
          if null rest
            then frontier'
            else M.insert c rest frontier'
        (_, h) =
          NEL.head a
        seen' =
          Set.insert h seen
        a' =
          filter (\(_, p) -> snd (NEL.head p) `Set.notMember` seen') (runRules h (toList a))
      in
        if null a'
          then a : go seen' frontier''
          else
            if Set.member h seen
              then a : go seen frontier''
              else go seen' (enqueue frontier'' a')
    enqueue =
      foldr (uncurry prepend)
    prepend c p =
      M.insertWith (<>) c [p]
    runRules h t =
      (\a -> (cost a, a)) <$> foldMap (run h t) (toList rs)
    run h t (l, r) =
      (\a' -> (l, a') :| t) <$> runRulePlated r h

normalise ::
  Algebra x ->
  Algebra x
normalise =
  rewrite arithmetic

normalisingRules ::
  Ord x =>
  [(RewriteLabel, Rule [] (Algebra x))]
normalisingRules =
  fmap wrap rules
  where
    wrap (RewriteIntroduceCardinality, r) =
      (RewriteIntroduceCardinality, r)
    wrap (l, Rule f) =
      (l, Rule (fmap normalise . f))

algebraSolutions ::
  Ord x =>
  Algebra x ->
  [(Cardinality, [(RewriteLabel, Algebra x)])]
algebraSolutions a =
  case normalise a of
    n@(Cardinality c) ->
      [(c, folded n)]
    n ->
      mapMaybe (solution n) (algebraSearch normalisingRules searchPathCost n)
  where
    solution n xs =
      case NEL.head xs of
        (_, Cardinality c) ->
          Just (c, toList xs <> folded n)
        _ ->
          Nothing
    folded n =
      if n == a
        then []
        else [(RewriteArithmetic, n)]

algebraCardinality ::
  Ord x =>
  Algebra x ->
  Maybe Cardinality
algebraCardinality =
  fmap fst . listToMaybe . algebraSolutions
