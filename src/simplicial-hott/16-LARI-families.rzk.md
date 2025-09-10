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

```rzk
#section LARI-families

#variable I : CUBE
#variable X : I → TOPE
#variable Y : X → TOPE
```

```rzk title="BW23, Definition 3.2.2"
#def is-LARI-family
  ( B : U)
  ( P : B → U)
  : U
  :=
    (g₀ : Y → B)
  → (f₀ : (y : Y) → P (g₀ y))
  → (g : (x : X) → B [Y x ↦ g₀ x])
  → has-initial ((x : X) → P (g x) [Y x ↦ f₀ x])
```

```rzk title="BW23, Corollary 3.2.4"
#def is-LARI-family-orthogonal-to
  ( B : U)
  ( P : B → U)
  ( orthogonal-to-P : orthogonal-to I X Y B P)
  : is-LARI-family B P
  := TODO (is-LARI-family B P)
```

```rzk
#section is-LARI-family-product

#variable J : U
#variable B : J → U
#variable P : (j : J) → B j → U
#variable is-LARI-family-P : (j : J) → is-LARI-family (B j) (P j)

```

```rzk title="BW23, Proposition 3.2.5"
#def is-LARI-family-product-is-LARI-family
  : is-LARI-family (total-type J B) (\ (j, b) → P j b)
  :=
  \ (g₀ : Y → total-type J B)
  ( f₀ : (y : Y) → P (π₁ (g₀ y)) (π₂ (g₀ y)))
  ( g : (x : X) → total-type J B [Y x ↦ g₀ x])
  → ( \ x → π₁ (is-LARI-family-P (π₁ (g x)) (\ _ → π₂ (g x)) f₀ (\ x → π₂ (g x))) x
    , \ (f : (x : X) → P (π₁ (g x)) (π₂ (g x)) [Y x ↦ f₀ x]) →
      TODO (is-contr
      ( hom ((x : X) → P (π₁ (g x)) (π₂ (g x)) [Y x ↦ f₀ x])
      ( \ x → π₂ (is-LARI-family-P (π₁ (g x)) (\ y → π₂ (g₀ y)) f₀ (\ x → π₂ (g x))) x)
      ( f))))
```

```rzk
#end is-LARI-family-product
```

```rzk
#end LARI-families
```
