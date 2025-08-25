# Find a home for this

```rzk
#lang rzk-1
```


```rzk
#def is-emb-rev
  ( A : U)
  ( x y : A)
  : is-emb (x = y) (y = x) (rev A x y)
  := is-emb-is-equiv (x = y) (y = x) (rev A x y) (π₂ (equiv-rev A x y))
```

```rzk
#def is-emb-total-type-is-emb-fiber
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → B a → C a)
  ( is-emb-f : (a : A) → is-emb (B a) (C a) (f a))
  : is-emb (total-type A B) (total-type A C) (\ (a, b) → (a, f a b))
  :=
  is-emb-is-prop-fib (total-type A B) (total-type A C) (\ (a, b) → (a, f a b))
  ( \ (a, c) → is-prop-Equiv-is-prop'
    ( fib (B a) (C a) (f a) c)
    ( fib (total-type A B) (total-type A C) (\ (a', b) → (a', f a' b)) (a, c))
    ( equiv-fib-total-map-fib-fiberwise A B C f (a, c))
    ( is-prop-fib-is-emb (B a) (C a) (f a) (is-emb-f a) c))
```

