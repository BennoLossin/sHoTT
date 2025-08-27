# LARI families

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Leibniz cotensor

```rzk
#def leibniz-cotensor-codomain
  ( Y X E B : U)
  ( j : Y → X)
  ( p : E → B)
  : U
  := Σ (f : Y → E) , Σ (g : X → B) , comp Y E B p f = comp Y X B g j

#def leibniz-cotensor-shape-codomain
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( E B : U)
  ( p : E → B)
  : U
  := Σ (f : Y → E) , Σ (g : X → B) , (\ (y : Y) → p (f y)) =_{ Y → B } (\ (y : Y) → g y)

#def leibniz-cotensor
  ( Y X E B : U)
  ( j : Y → X)
  ( p : E → B)
  ( f : X → E)
  : leibniz-cotensor-codomain Y X E B j p
  := (comp Y X E f j , (comp X E B p f , refl))

#def leibniz-cotensor-shape
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( E B : U)
  ( p : E → B)
  ( f : X → E)
  : leibniz-cotensor-shape-codomain I X Y E B p
  := (\ (y : Y) → f y , (\ (x : X) → p (f x), refl))
```

## LARI families

```rzk title="BW23, Definition 3.2.2"
#def is-LARI-family
  ( Y X B : U)
  ( j : Y → X)
  ( P : B → U)
  : U
  :=
  has-initial-section
  ( leibniz-cotensor-codomain Y X (total-type B P) B j (projection-total-type B P))
  ( fib
    ( X → total-type B P)
    ( leibniz-cotensor-codomain Y X (total-type B P) B j (projection-total-type B P))
    ( leibniz-cotensor Y X (total-type B P) B j (projection-total-type B P)))

#def is-LARI-shape-family
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( B : U)
  ( P : B → U)
  : U
  :=
  has-initial-section
  ( leibniz-cotensor-shape-codomain I X Y (total-type B P) B (projection-total-type B P))
  ( fib
    ( X → total-type B P)
    ( leibniz-cotensor-shape-codomain I X Y (total-type B P) B (projection-total-type B P))
    ( leibniz-cotensor-shape I X Y (total-type B P) B (projection-total-type B P)))
```
