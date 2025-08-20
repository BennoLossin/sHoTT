# Full Embeddings

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#assume TODO : (A : U) → A
#assume funext : FunExt
-- #assume extext : ExtExt
```

```rzk
#section full-embeddings

#variables A B : U
#variable f : A → B

#def is-full-emb
  : U
  :=
    (x : A)
  → (y : A)
  → is-equiv (hom A x y) (hom B (f x) (f y)) (ap-hom A B f x y)

#def is-full-emb-is-emb-has-arrow-lifts
  ( is-emb-f : is-emb A B f)
  ( has-arrow-lifts : (g : Δ¹ → B) → (fib A B f (g 0₂)) → (fib A B f (g 1₂)) → ((t : Δ¹) → fib A B f (g t)))
  : is-full-emb
  := TODO is-full-emb



```

### Full Embeddings are Embeddings

```rzkk
#def
```

```rzkk
#def is-emb-is-full-emb
  ( is-full-emb-f : is-full-emb)
  : is-emb A B f
  := π₁ is-full-emb-f
```

```rzk
#end full-embeddings
```

```rzk


#def is-full-emb-total-type-is-full-emb-fiber
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → B a → C a)
  ( is-full-emb-f : (a : A) → is-full-emb (B a) (C a) (f a))
  : is-full-emb (total-type A B) (total-type A C) (\ (a, b) → (a, f a b))
  :=
  TODO (is-full-emb (total-type A B) (total-type A C) (\ (a, b) → (a, f a b)))

```

```rzk
#def is-full-emb-rev
  ( A : U)
  ( x y : A)
  : is-full-emb (x = y) (y = x) (rev A x y)
  := TODO (is-full-emb (x = y) (y = x) (rev A x y))
```

```rzk
#def is-full-emb-is-equiv
  ( A : U)
  ( B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : is-full-emb A B f
  := TODO (is-full-emb A B f)
```

```rzk
#def is-full-emb-subtype-projection
  ( A : U)
  ( P : A → U)
  ( is-predicate-P : is-predicate A P)
  : is-full-emb (total-type A P) A (projection-total-type A P)
  := TODO (is-full-emb (total-type A P) A (projection-total-type A P))
```

```rzk
#def is-full-emb-quadruple-comp
  ( A B C D E : U)
  ( f : A → B)
  ( is-full-emb-f : is-full-emb A B f)
  ( g : B → C)
  ( is-full-emb-g : is-full-emb B C g)
  ( h : C → D)
  ( is-full-emb-h : is-full-emb C D h)
  ( i : D → E)
  ( is-full-emb-i : is-full-emb D E i)
  : is-full-emb A E (quadruple-comp A B C D E i h g f)
  :=
  \ x y → rev-transport ((hom A x y) → (hom E (i (h (g (f x)))) (i (h (g (f y))))))
  ( \ gg → is-equiv (hom A x y) (hom E (i (h (g (f x)))) (i (h (g (f y))))) gg)
  ( ap-hom A E (quadruple-comp A B C D E i h g f) x y)
  ( \ p → ap-hom D E i (h (g (f x))) (h (g (f y)))
    ( ap-hom C D h (g (f x)) (g (f y)) (ap-hom B C g (f x) (f y) (ap-hom A B f x y p))))
  ( eq-htpy funext (hom A x y) (\ _ → hom E (i (h (g (f x)))) (i (h (g (f y)))))
    ( ap-hom A E (quadruple-comp A B C D E i h g f) x y)
    ( \ p → ap-hom D E i (h (g (f x))) (h (g (f y)))
      ( ap-hom C D h (g (f x)) (g (f y)) (ap-hom B C g (f x) (f y) (ap-hom A B f x y p))))
    ( ap-hom-quadruple-comp A B C D E x y f g h i))
  ( is-equiv-quadruple-comp
    ( hom A x y)
    ( hom B (f x) (f y))
    ( hom C (g (f x)) (g (f y)))
    ( hom D (h (g (f x))) (h (g (f y))))
    ( hom E (i (h (g (f x)))) (i (h (g (f y)))))
    ( ap-hom A B f x y)
    ( is-full-emb-f x y)
    ( ap-hom B C g (f x) (f y))
    ( is-full-emb-g (f x) (f y))
    ( ap-hom C D h (g (f x)) (g (f y)))
    ( is-full-emb-h (g (f x)) (g (f y)))
    ( ap-hom D E i (h (g (f x))) (h (g (f y))))
    ( is-full-emb-i (h (g (f x))) (h (g (f y)))))
```
