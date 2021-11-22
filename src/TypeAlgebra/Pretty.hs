module TypeAlgebra.Pretty
  ( rewriteLabel,
    mathjaxSolution,
    prettySolution,
    prettyPrec,
  )
where

import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty ((:|)), toList)
import qualified Data.List.NonEmpty as NEL
import TypeAlgebra.Algebra (Algebra (..))
import TypeAlgebra.Rules (RewriteLabel (..))

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

mathjaxSolution :: Algebra String -> NonEmpty (RewriteLabel, Algebra String) -> String
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
