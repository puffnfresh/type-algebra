{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.Map as M
import Hedgehog (Gen, Group (..), Property, checkParallel, forAll, property, withTests, (===))
import Hedgehog.Gen (element, unicodeAll)
import Hedgehog.Main (defaultMain)
import TypeAlgebra (Algebra (..), RewriteLabel (RewriteArithmetic), Variance (..), algebraArity, algebraSolutions, variance)

main :: IO ()
main =
  defaultMain
    [ checkParallel
        ( Group
            "TypeAlgebra"
            [ ("Variance semigroup laws", propertyVarianceSemigroup),
              ("variance singleton", propertyVarianceSingleton),
              ("variance invariant", propertyVarianceInvariant),
              ("variance negative", propertyVarianceNegative),
              ("variance forall", propertyVarianceForall),
              ("variance equivalence", propertyVarianceEquivalence),
              ("no repetitive rewrites in solutions", propertyRemoveDuplicates),
              ("2 -> 2", propertyExampleBoolBool),
              ("∀ a. ∀ b. (a -> b) -> (a + 1) -> (b + 1)", propertyExampleMapMaybe),
              ("∀ x. x -> x", propertyExampleIdentity),
              ("∀ x. x -> (x * x)", propertyExampleOne),
              ("∀ x. x -> (x + x)", propertyExampleTwo)
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
    variance (Exponent (Exponent (Arity 2) (Var name)) (Var name))
      === M.fromList
        [ (name, Contravariant)
        ]

propertyRemoveDuplicates :: Property
propertyRemoveDuplicates =
  withTests 1 . property $ do
    let example = Exponent (Sum (Arity 1) (Arity 2)) (Arity 3) :: Algebra ()
    algebraSolutions example
      === [ (RewriteArithmetic, Arity 27)
              :| [(RewriteArithmetic, Exponent (Arity 3) (Arity 3))]
          ]

propertyExampleBoolBool :: Property
propertyExampleBoolBool =
  withTests 1 . property $ do
    let example = Exponent (Arity 2) (Arity 2) :: Algebra ()
    algebraArity example === Just 4

propertyExampleMapMaybe :: Property
propertyExampleMapMaybe =
  withTests 1 . property $ do
    let example =
          Forall
            ("a" :: String)
            ( Forall
                "b"
                ( Exponent
                    (Exponent (Sum (Var "a") (Arity 1)) (Sum (Var "b") (Arity 1)))
                    (Exponent (Var "a") (Var "b"))
                )
            )
    algebraArity example === Just 2

propertyExampleIdentity :: Property
propertyExampleIdentity =
  withTests 1 . property $ do
    let example = Forall ("x" :: String) (Exponent (Var "x") (Var "x"))
    algebraArity example === Just 1

propertyExampleOne :: Property
propertyExampleOne =
  withTests 1 . property $ do
    let example = Forall ("x" :: String) (Exponent (Product (Var "x") (Var "x")) (Var "x"))
    algebraArity example === Just 1

propertyExampleTwo :: Property
propertyExampleTwo =
  withTests 1 . property $ do
    let example = Forall ("x" :: String) (Exponent (Sum (Var "x") (Var "x")) (Var "x"))
    algebraArity example === Just 2
