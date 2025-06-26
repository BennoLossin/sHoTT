# Final sections

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
-- #assume extext : ExtExt
```

## Initial definitions

```rzk
#def has-final-section
  ( A : U)
  ( B : A → U)
  : U
  := Σ (s : (a : A) → B a) , (a : A) → is-final (B a) (s a)
```

We want to show that this actually defines a LARI family. For the proof of this,
we need to the auxiliary notion of a dependent final section.

## Dependent final sections

Next, an a priori more restrictive definition for finality.

```rzk
#def has-dhom-final-section
  ( A : U)
  ( B : A → U)
  : U
  :=
  Σ ( s : (a : A) → B a)
  , ( a : A) → (a' : A) → (b : B a) → (f : hom A a a')
    → is-contr (dhom A a a' f B b (s a'))
```

We will now show that these are actually the same. The first direction is
simple:

```rzk
#def has-final-section-has-dhom-final-section
    ( A : U)
    ( B : A → U)
    ( has-dhom-final-section-B : has-dhom-final-section A B)
    : has-final-section A B
    :=
    ( π₁ has-dhom-final-section-B
    , \ (a : A) (b : B a)
      → is-contr-equiv-is-contr
        ( dhom A a a (id-hom A a) B b (π₁ has-dhom-final-section-B a))
        ( hom (B a) b (π₁ has-dhom-final-section-B a))
        ( equiv-hom-dhom A a B b (π₁ has-dhom-final-section-B a))
        ( π₂ has-dhom-final-section-B a a b (id-hom A a)))
```

```rzkk
#def has-dhom-final-section-has-final-section
  ( A : U)
  ( B : A → U)
  ( has-final-section-B : has-final-section A B)
  : has-dhom-final-section A B
  :=
  ( π₁ has-final-section-B
  , \ (a : A) → (a' : A) → (b : B a) → (f : hom A a a')
  → ( \ t → s (f t)
    , \ (g : dhom A a a' f B b (s a')) → {- ^ = g -}))

```

## Final section are LARI

```rzk
#assume TODO : (A : U) → A

#section is-transposing-LARI-has-final-section
#variable A : U
#variable B : A → U
#variable has-final-section-B : has-final-section A B


#def X
  ( a a' : A)
  ( f : hom A a a')
  ( b : B a)
  : is-contr (dhom A a a' f B b (π₁ has-final-section-B a'))
  := TODO (is-contr (dhom A a a' f B b (π₁ has-final-section-B a')))

#def projection-section-has-final-section
  : A → total-type A B
  := \ a → (a, π₁ has-final-section-B a)

#def is-transposing-adj-has-final-section uses (has-final-section-B)
  : is-transposing-adj (total-type A B) A
    ( projection-total-type A B)
    ( projection-section-has-final-section)
  :=
  \ (a , b) a' → equiv-comp
    ( hom A a a')
    ( Σ ( f : hom A a a') , dhom A a a' f B b (π₁ has-final-section-B a'))
    ( hom (total-type A B) (a, b) (a', π₁ has-final-section-B a'))
    ( inv-equiv
      ( Σ ( f : hom A a a') , dhom A a a' f B b (π₁ has-final-section-B a'))
      ( hom A a a')
      ( equiv-total-type-is-contr
        ( hom A a a')
        ( \ f → dhom A a a' f B b (π₁ has-final-section-B a'))
        ( \ f → X a a' f b)))
    ( equiv-sigma-dhom-hom A B (a , b) (a' , π₁ has-final-section-B a'))
```

```rzkk
#def is-transposing-LARI-has-final-section
  ( is-segal-total : is-segal (total-type A B))
  : is-transposing-LARI (total-type A B) A is-segal-total
    ( projection-total-type A B)
  :=
  (\ (f : (total-type A B) → A)
    (u : A → total-type A B)
  →
  (\ (adj : is-transposing-adj (total-type A B) A f u)
  →
  ( u
  , ( adj
    , \ ((a , b) : total-type A B) → TODO
      ( is-iso-arrow
        ( total-type A B)
        ( is-segal-total)
        ( a , b)
        ( u (f (a , b)))
        ( π₁
          ( adj (a , b) (f (a, b)))
          ( id-hom A (f (a , b)))))))
  )
  ( TODO (is-transposing-adj (total-type A B) A f u)) -- =: adj
  )
  ( projection-total-type A B) -- =: f
  ( \ a → (a, π₁ has-final-section-B a)) -- =: u
```

```rzk
#end is-transposing-LARI-has-final-section
```
