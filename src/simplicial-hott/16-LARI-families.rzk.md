# LARI families

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#assume TODO : (A : U) → A
#assume extext : ExtExt
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

```rzk title="BW23, Corollary 3.2.4"
#def is-LARI-shape-family-orthogonal-to
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( B : U)
  ( P : B → U)
  ( orthogonal-to-P : orthogonal-to I X Y B P)
  : is-LARI-shape-family I X Y B P
  :=
  has-initial-section-is-equiv extext
  ( X → total-type B P)
  ( leibniz-cotensor-shape-codomain I X Y (total-type B P) B (projection-total-type B P))
  ( leibniz-cotensor-shape I X Y (total-type B P) B (projection-total-type B P))
  ( is-equiv-leibniz-cotensor-shap-orthogonal-to TODO I X Y B P)
```

```rzkk
#section is-LARI-shape-family-product

#variable I : CUBE
#variable X : I → TOPE
#variable Y : X → TOPE
#variable J : U
#variable B : J → U
#variable P : (j : J) → B j → U
#variable is-LARI-shape-family-P : (j : J) → is-LARI-shape-family I X Y (B j) (P j)

#def initial-section-is-LARI-shape-family-product
  ( (f, (g, p)) : leibniz-cotensor-shape-codomain I X Y
    ( total-type (total-type J B) (\ (j, b) → P j b))
    ( total-type J B)
    ( projection-total-type (total-type J B) (\ (j, b) → P j b)))
  : fib
    ( X → total-type (total-type J B) (\ (j, b) → P j b))
    ( leibniz-cotensor-shape-codomain I X Y
      ( total-type (total-type J B) (\ (j, b) → P j b))
      ( total-type J B)
      ( projection-total-type (total-type J B) (\ (j, b) → P j b)))
    ( leibniz-cotensor-shape I X Y
      ( total-type (total-type J B) (\ (j, b) → P j b))
      ( total-type J B)
      ( projection-total-type (total-type J B) (\ (j, b) → P j b)))
    ( f, (g, p))
  :=
  {-

  f : Y → total-type (total-type J B) (\ (j, b) → P j b)
  g : X → total-type J B
  p : (\ y → projection-total-type (f y)) = (\ y → g y)


  -}
  ( {-F:=-} \ x → (g x, π₁ (is-LARI-shape-family-P (π₁ (g x)))
    ( \ y → f y
    , ( \ x →
      , ? )))
  , lcs F = (f, (g, p)))


```

```rzkk title="BW23, Proposition 3.2.5"
#def is-LARI-shape-family-product
  : is-LARI-shape-family I X Y (total-type J B) (\ (j, b) → P j b)
  :=
  TODO (has-initial-section
  ( leibniz-cotensor-shape-codomain I X Y
    ( total-type (total-type J B) (\ (j, b) → P j b))
    ( total-type J B)
    ( projection-total-type (total-type J B) (\ (j, b) → P j b)))
  ( fib
    ( X → total-type (total-type J B) (\ (j, b) → P j b))
    ( leibniz-cotensor-shape-codomain I X Y
      ( total-type (total-type J B) (\ (j, b) → P j b))
      ( total-type J B)
      ( projection-total-type (total-type J B) (\ (j, b) → P j b)))
    ( leibniz-cotensor-shape I X Y
      ( total-type (total-type J B) (\ (j, b) → P j b))
      ( total-type J B)
      ( projection-total-type (total-type J B) (\ (j, b) → P j b)))))
```

```rzkk
#end is-LARI-shape-family-product
```
