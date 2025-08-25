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

## Leibniz cotensor

```rzk
#def leibniz-cotensor-codomain
  ( Y X E B : U)
  ( j : Y → X)
  ( p : E → B)
  : U
  := Σ (f : Y → E) , Σ (g : X → B) , comp Y E B p f = comp Y X B g j

#def leibniz-cotensor
  ( Y X E B : U)
  ( j : Y → X)
  ( p : E → B)
  ( f : X → E)
  : leibniz-cotensor-codomain Y X E B j p
  := (comp Y X E f j , (comp X E B p f , refl))

```

## LARI families

```rzk title="BW23, Definition 3.2.2"
#def is-LARI-family
  ( Y X B : U)
  ( j : Y → X)
  ( P : B → U)
  ( S : is-segal (X → total-type B P)) -- TODO: make this requirement simpler
  : U
  :=
  is-transposing-LARI
    ( X → total-type B P)
    ( leibniz-cotensor-codomain Y X (total-type B P) B j (projection-total-type B P))
    S
    ( leibniz-cotensor Y X (total-type B P) B j (projection-total-type B P))
```
