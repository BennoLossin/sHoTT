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
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( B : U)
  ( P : B → U)
  : U
  :=
    (g₀ : Y → B)
  → (f : (y : Y) → P (g₀ y))
  → (g : (x : X) → B [Y x ↦ g₀ x])
  → has-initial ((x : X) → P (g x) [Y x ↦ f x])
```

```rzk title="BW23, Corollary 3.2.4"
#def is-LARI-family-orthogonal-to
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( B : U)
  ( P : B → U)
  ( orthogonal-to-P : orthogonal-to I X Y B P)
  : is-LARI-family I X Y B P
  := TODO (is-LARI-family I X Y B P)
```

```rzk
#section is-LARI-family-product

#variable I : CUBE
#variable X : I → TOPE
#variable Y : X → TOPE
#variable J : U
#variable B : J → U
#variable P : (j : J) → B j → U
#variable is-LARI-family-P : (j : J) → is-LARI-family I X Y (B j) (P j)

```

```rzk title="BW23, Proposition 3.2.5"
#def is-LARI-family-product-is-LARI-family
  : is-LARI-family I X Y (total-type J B) (\ (j, b) → P j b)
  :=
  \ (g₀ : Y → total-type J B)
  ( f : (y : Y) → P (π₁ (g₀ y)) (π₂ (g₀ y)))
  ( g : (x : X) → total-type J B [Y x ↦ g₀ x])
  → ( \ x → π₂ (is-LARI-family-P (π₁ (g x)) (\ y → π₂ (g₀ y)) f (\ x → π₂ (g x))) x
    , TODO )
```

```rzk
#end is-LARI-family-product
```
