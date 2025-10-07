# Left adjoint right inverse (LARI) adjunctions

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Basic definitions

```rzk title="BW23, Definition B.1.1"
#def is-transposing-LARI-adj
  ( A B : U)
  ( is-segal-A : is-segal A)
  ( f : A → B)
  ( u : B → A)
  ( adj : is-transposing-adj A B f u)
  : U
  :=
  ( a : A)
  → is-iso-arrow A is-segal-A a (u (f a)) (π₁ (adj a (f a)) (id-hom B (f a)))

#def is-transposing-LARI
  ( A B : U)
  ( is-segal-A : is-segal A)
  ( f : A → B)
  : U
  :=
  Σ ( u : B → A)
  , ( Σ ( adj : is-transposing-adj A B f u)
    , is-transposing-LARI-adj A B is-segal-A f u adj)
```

```rzk
#def has-transposing-LARI-adj
  ( A B : U)
  ( is-segal-A : is-segal A)
  ( f : A → B)
  : U
  :=
  Σ (u : B → A)
  , Σ (adj : is-transposing-adj A B f u)
    , is-transposing-LARI-adj A B is-segal-A f u adj
```
