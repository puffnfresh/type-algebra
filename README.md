# Type Algebra

Largely based on Alex's work on [Counting type inhabitants](https://alexknvl.com/posts/counting-type-inhabitants.html).

We can perform algebra on types. For example, given a polymorphic type:

```
∀ a. ∀ b. (a -> b) -> a + 1 -> b + 1
= ∀ a. a + 1 -> a + 1   -- via covariant yoneda lemma
= ∀ a. (a -> a + 1) * (1 -> a + 1)      -- via curry sum
= ∀ a. (a -> a + 1) * (a + 1)   -- via arithmetic
= (∀ a. a -> a + 1) * (∀ a. a + 1)      -- via distributive
= (∀ a. (1 -> a) -> a + 1) * (∀ a. a + 1)       -- via introduce arity
= (1 + 1) * (∀ a. a + 1)        -- via covariant yoneda lemma
= 2 * (∀ a. a + 1)      -- via arithmetic
= 2 * (∀ a. (0 -> a) -> a + 1)  -- via introduce arity
= 2 * (0 + 1)   -- via covariant yoneda lemma
= 2 * 1 -- via arithmetic
= 2     -- via arithmetic
```

The above proof output was generated via:

```haskell
x :: Algebra String
x =
  Forall "a"
    (Forall "b"
      ( (Var "a" ->> Var "b") ->>
        (Sum (Var "a") (Arity 1) ->>
        Sum (Var "b") (Arity 1))))

traverse_ (putStrLn . prettySolution  x) (take 1 (algebraSolutions x))
```

And the proof can also be pretty printed to LaTeX/MathJax:

```math
\begin{align*}
\forall a. \forall b. (a \rightarrow b) \rightarrow ((a + 1) \rightarrow (b + 1)) &= \forall a. (a + 1) \rightarrow (a + 1) && \text{(covariant yoneda lemma)}
\\
&= \forall a. a \rightarrow (a + 1) * 1 \rightarrow (a + 1) && \text{(curry sum)}
\\
&= \forall a. a \rightarrow (a + 1) * (a + 1) && \text{(arithmetic)}
\\
&= (\forall a. a \rightarrow (a + 1)) * (\forall a. a + 1) && \text{(distributive)}
\\
&= (\forall a. (1 \rightarrow a) \rightarrow (a + 1)) * (\forall a. a + 1) && \text{(introduce arity)}\\
&= (1 + 1) * (\forall a. a + 1) && \text{(covariant yoneda lemma)}
\\
&= 2 * (\forall a. a + 1) && \text{(arithmetic)}
\\
&= 2 * (\forall a. (0 \rightarrow a) \rightarrow (a + 1)) && \text{(introduce arity)}
\\
&= 2 * (0 + 1) && \text{(covariant yoneda lemma)}
\\
&= 2 * 1 && \text{(arithmetic)}
\\
&= 2 && \text{(arithmetic)}
\end{align*}
```
