module TypeAlgebra
  ( module TypeAlgebra.Algebra,
    algebraSolutions,
    algebraArity,
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
import Data.Ord (comparing)
import qualified Data.Set as Set
import TypeAlgebra.Algebra (Algebra (..), Variance (..), subst, variance)
import TypeAlgebra.Rules (RewriteLabel, Rule, rules, runRulePlated)

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
