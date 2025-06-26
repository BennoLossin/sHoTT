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

## Final section are LARI families

```rzkk
#def grothendiek-section-has-terminal-section
  ( B : U)
  ( A : B → U)
  ( has-terminal-section-A : has-terminal-section A)
  : B → total-type B A
  := \ (b : B) → (b , π₁ has-terminal-section-A b)
```

```rzk
#def is-LARI-family-has-final-section
  ( A : U)
  ( B : A → U)
  ( has-terminal-section-B : has-terminal-section A B)
  : is-LARI-family
```
