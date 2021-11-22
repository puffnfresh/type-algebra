# Type Algebra

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

![](https://render.githubusercontent.com/render/math?math=%5Cbegin%7Balign*%7D%0A%5Cforall%20a.%20%5Cforall%20b.%20(a%20%5Crightarrow%20b)%20%5Crightarrow%20((a%20%2B%201)%20%5Crightarrow%20(b%20%2B%201))%20%26%3D%20%5Cforall%20a.%20(a%20%2B%201)%20%5Crightarrow%20(a%20%2B%201)%20%26%26%20%5Ctext%7B(covariant%20yoneda%20lemma)%7D%0A%5C%5C%0A%26%3D%20%5Cforall%20a.%20a%20%5Crightarrow%20(a%20%2B%201)%20*%201%20%5Crightarrow%20(a%20%2B%201)%20%26%26%20%5Ctext%7B(curry%20sum)%7D%0A%5C%5C%0A%26%3D%20%5Cforall%20a.%20a%20%5Crightarrow%20(a%20%2B%201)%20*%20(a%20%2B%201)%20%26%26%20%5Ctext%7B(arithmetic)%7D%0A%5C%5C%0A%26%3D%20(%5Cforall%20a.%20a%20%5Crightarrow%20(a%20%2B%201))%20*%20(%5Cforall%20a.%20a%20%2B%201)%20%26%26%20%5Ctext%7B(distributive)%7D%0A%5C%5C%0A%26%3D%20(%5Cforall%20a.%20(1%20%5Crightarrow%20a)%20%5Crightarrow%20(a%20%2B%201))%20*%20(%5Cforall%20a.%20a%20%2B%201)%20%26%26%20%5Ctext%7B(introduce%20arity)%7D%5C%5C%0A%26%3D%20(1%20%2B%201)%20*%20(%5Cforall%20a.%20a%20%2B%201)%20%26%26%20%5Ctext%7B(covariant%20yoneda%20lemma)%7D%0A%5C%5C%0A%26%3D%202%20*%20(%5Cforall%20a.%20a%20%2B%201)%20%26%26%20%5Ctext%7B(arithmetic)%7D%0A%5C%5C%0A%26%3D%202%20*%20(%5Cforall%20a.%20(0%20%5Crightarrow%20a)%20%5Crightarrow%20(a%20%2B%201))%20%26%26%20%5Ctext%7B(introduce%20arity)%7D%0A%5C%5C%0A%26%3D%202%20*%20(0%20%2B%201)%20%26%26%20%5Ctext%7B(covariant%20yoneda%20lemma)%7D%0A%5C%5C%0A%26%3D%202%20*%201%20%26%26%20%5Ctext%7B(arithmetic)%7D%0A%5C%5C%0A%26%3D%202%20%26%26%20%5Ctext%7B(arithmetic)%7D%0A%5Cend%7Balign*%7D)
