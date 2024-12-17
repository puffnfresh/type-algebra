{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.Map as M
import Hedgehog (Gen, Group (..), Property, checkParallel, forAll, property, withTests, (===))
import Hedgehog.Gen (element, unicodeAll)
import Hedgehog.Main (defaultMain)
import TypeAlgebra (Algebra (..), Cardinality (..), Variance (..), algebraCardinality, algebraSolutions, variance)
import TypeAlgebra.Rules (RewriteLabel (RewriteArithmetic))

main :: IO ()
main =
  defaultMain
    [ checkParallel
        ( Group
            "TypeAlgebra.Algebra"
            [ ("variance semigroup laws", propertyVarianceSemigroup),
              ("variance singleton", propertyVarianceSingleton),
              ("variance invariant", propertyVarianceInvariant),
              ("variance negative", propertyVarianceNegative),
              ("variance forall", propertyVarianceForall),
              ("variance equivalence", propertyVarianceEquivalence)
            ]
        ),
      checkParallel
        ( Group
            "TypeAlgebra"
            [ ("no repetitive rewrites in solution", propertyRemoveDuplicates),
              ("2 -> 2", propertyExampleBoolBool),
              ("∀ a. ∀ b. (a -> b) -> (a + 1) -> (b + 1)", propertyExampleMapMaybe),
              ("∀ x. x -> x", propertyExampleIdentity),
              ("∀ x. x -> (x * x)", propertyExampleOne),
              ("∀ x. x -> (x + x)", propertyExampleTwo),
              ("∀ x. (x, x) -> (x, x)", propertyExamplePair),
              ("∀ a b c. (a -> b) -> (b -> c) -> a -> c", propertyExampleCompose),
              ("∞ -> 2", propertyExampleInfiniteTwo)
            ]
        )
    ]

genVariance :: Gen Variance
genVariance =
  element [Covariant, Contravariant, Invariant]

propertyVarianceSemigroup :: Property
propertyVarianceSemigroup =
  property $ do
    x <- forAll genVariance
    y <- forAll genVariance
    z <- forAll genVariance
    (x <> y) <> z === x <> (y <> z)

propertyVarianceSingleton :: Property
propertyVarianceSingleton =
  property $ do
    name <- forAll unicodeAll
    variance (Var name) === M.singleton name Covariant

propertyVarianceInvariant :: Property
propertyVarianceInvariant =
  property $ do
    name <- forAll unicodeAll
    variance (Exponent (Var name) (Var name)) === M.singleton name Invariant

propertyVarianceNegative :: Property
propertyVarianceNegative =
  property $ do
    name <- forAll unicodeAll
    let name' = succ name
    variance (Exponent (Var name) (Var name'))
      === M.fromList
        [ (name, Covariant),
          (name', Contravariant)
        ]

propertyVarianceForall :: Property
propertyVarianceForall =
  property $ do
    name <- forAll unicodeAll
    let name' = succ name
    variance (Exponent (Var name) (Forall name' (Var name')))
      === M.fromList
        [ (name, Covariant)
        ]

propertyVarianceEquivalence :: Property
propertyVarianceEquivalence =
  property $ do
    name <- forAll unicodeAll
    variance (Exponent (Exponent (Cardinality (Finite 2)) (Var name)) (Var name))
      === M.fromList
        [ (name, Contravariant)
        ]

propertyRemoveDuplicates :: Property
propertyRemoveDuplicates =
  withTests 1 . property $ do
    let example = Exponent (Sum (Cardinality (Finite 1)) (Cardinality (Finite 2))) (Cardinality (Finite 3)) :: Algebra ()
    algebraSolutions example
      === [ (RewriteArithmetic, Cardinality (Finite 27))
              :| [(RewriteArithmetic, Exponent (Cardinality (Finite 3)) (Cardinality (Finite 3)))]
          ]

propertyExampleBoolBool :: Property
propertyExampleBoolBool =
  withTests 1 . property $ do
    let example = Exponent (Cardinality (Finite 2)) (Cardinality (Finite 2)) :: Algebra ()
    algebraCardinality example === Just (Finite 4)

propertyExamplePair :: Property
propertyExamplePair =
  withTests 1 . property $ do
    let example =
          Forall
            ("a" :: String)
            (Exponent (Product (Var "a") (Var "a")) (Product (Var "a") (Var "a")))
    algebraCardinality example === Just (Finite 4)

propertyExampleCompose :: Property
propertyExampleCompose =
  withTests 1 . property $ do
    let example =
          Forall
            ("a" :: String)
            ( Forall
                "b"
                ( Forall
                    "c"
                    ( (Exponent (Exponent (Exponent (Var "c") (Var "a")) (Exponent (Var "c") (Var "b"))) (Exponent (Var "b") (Var "a")))
                    )
                )
            )
    algebraCardinality example === Just (Finite 1)

propertyExampleMapMaybe :: Property
propertyExampleMapMaybe =
  withTests 1 . property $ do
    let example =
          Forall
            ("a" :: String)
            ( Forall
                "b"
                ( Exponent
                    (Exponent (Sum (Var "a") (Cardinality (Finite 1))) (Sum (Var "b") (Cardinality (Finite 1))))
                    (Exponent (Var "a") (Var "b"))
                )
            )
    algebraCardinality example === Just (Finite 2)

propertyExampleIdentity :: Property
propertyExampleIdentity =
  withTests 1 . property $ do
    let example = Forall ("x" :: String) (Exponent (Var "x") (Var "x"))
    algebraCardinality example === Just (Finite 1)

propertyExampleOne :: Property
propertyExampleOne =
  withTests 1 . property $ do
    let example = Forall ("x" :: String) (Exponent (Product (Var "x") (Var "x")) (Var "x"))
    algebraCardinality example === Just (Finite 1)

propertyExampleTwo :: Property
propertyExampleTwo =
  withTests 1 . property $ do
    let example = Forall ("x" :: String) (Exponent (Sum (Var "x") (Var "x")) (Var "x"))
    algebraCardinality example === Just (Finite 2)

propertyExampleInfiniteTwo :: Property
propertyExampleInfiniteTwo =
  withTests 1 . property $ do
    let example = Forall ("x" :: String) (Exponent (Exponent (Sum (Var "x") (Var "x")) (Var "x")) (Cardinality Infinite))
    algebraCardinality example === Just Infinite
