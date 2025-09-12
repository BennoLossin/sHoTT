# LARI families

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#assume TODO : (A : U) → A
#assume extext : ExtExt
#assume weakfunext : WeakFunExt
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

```rzk
#def product-lift-is-LARI-family
  ( g₀ : Y → ((j : J) → B j))
  ( f₀ : (y : Y) → (j : J) → P j (g₀ y j))
  ( g : (x : X) → ((j : J) → B j) [Y x ↦ g₀ x])
  : (x : X) → ((j : J) → P j (g x j)) [Y x ↦ f₀ x]
  := \ x j → π₁ (is-LARI-family-P j
      ( \ y → g₀ y j)
      ( \ y → f₀ y j)
      ( \ x → g x j)) x

#def is-weakly-contr-hom-product-lift
  ( g₀ : Y → ((j : J) → B j))
  ( f₀ : (y : Y) → (j : J) → P j (g₀ y j))
  ( g : (x : X) → ((j : J) → B j) [Y x ↦ g₀ x])
  ( f : (x : X) → ((j : J) → P j (g x j)) [Y x ↦ f₀ x])
  : (j : J) → is-contr (hom
    ( (x : X) → P j (g x j) [Y x ↦ f₀ x j])
    ( \ x → product-lift-is-LARI-family g₀ f₀ g x j)
    ( \ x → f x j))
  :=
  \ j → π₂
  ( is-LARI-family-P j
    ( \ y → g₀ y j)
    ( \ y → f₀ y j)
    ( \ x → g x j))
  ( \ x → f x j)

#def is-contr-fun-hom-product-lift uses (is-LARI-family-P)
  ( g₀ : Y → ((j : J) → B j))
  ( f₀ : (y : Y) → (j : J) → P j (g₀ y j))
  ( g : (x : X) → ((j : J) → B j) [Y x ↦ g₀ x])
  ( f : (x : X) → ((j : J) → P j (g x j)) [Y x ↦ f₀ x])
  : is-contr ((j : J) → hom
    ( (x : X) → P j (g x j) [Y x ↦ f₀ x j])
    ( \ x → product-lift-is-LARI-family g₀ f₀ g x j)
    ( \ x → f x j))
  :=
  weakfunext
  ( J)
  ( \ j → hom
    ( (x : X) → P j (g x j) [Y x ↦ f₀ x j])
    ( \ x → product-lift-is-LARI-family g₀ f₀ g x j)
    ( \ x → f x j))
  ( is-weakly-contr-hom-product-lift g₀ f₀ g f)

#def is-contr-hom-product-lift uses (is-LARI-family-P weakfunext)
  ( g₀ : Y → ((j : J) → B j))
  ( f₀ : (y : Y) → (j : J) → P j (g₀ y j))
  ( g : (x : X) → ((j : J) → B j) [Y x ↦ g₀ x])
  ( f : (x : X) → ((j : J) → P j (g x j)) [Y x ↦ f₀ x])
  : is-contr (hom
    ( (j : J) → (x : X) → P j (g x j) [Y x ↦ f₀ x j])
    ( \ j x → product-lift-is-LARI-family g₀ f₀ g x j)
    ( \ j x → f x j))
  :=
  is-contr-is-equiv-is-contr
  ( (j : J) → hom
    ( (x : X) → P j (g x j) [Y x ↦ f₀ x j])
    ( \ x → product-lift-is-LARI-family g₀ f₀ g x j)
    ( \ x → f x j))
  ( hom
    ( (j : J) → (x : X) → P j (g x j) [Y x ↦ f₀ x j])
    ( \ j x → product-lift-is-LARI-family g₀ f₀ g x j)
    ( \ j x → f x j))
  ( flip-ext-fun-inv 2 Δ¹ ∂Δ¹
    ( J)
    ( \ _ j → ((x : X) → P j (g x j) [Y x ↦ f₀ x j]))
    ( \ t j → recOR(
        t ≡ 0₂ ↦ ( \ (x : I | X x) → product-lift-is-LARI-family g₀ f₀ g x j)
      , t ≡ 1₂ ↦ ( \ (x : I | X x) → f x j))))
  ( is-contr-fun-hom-product-lift g₀ f₀ g f)

#def equiv-hom-flipped-product-lift uses (is-LARI-family-P)
  ( g₀ : Y → ((j : J) → B j))
  ( f₀ : (y : Y) → (j : J) → P j (g₀ y j))
  ( g : (x : X) → ((j : J) → B j) [Y x ↦ g₀ x])
  ( f : (x : X) → ((j : J) → P j (g x j)) [Y x ↦ f₀ x])
  : Equiv
  ( hom
    ( (j : J) → (x : X) → P j (g x j) [Y x ↦ f₀ x j])
    ( \ j x → product-lift-is-LARI-family g₀ f₀ g x j)
    ( \ j x → f x j))
  ( hom
    ( (x : X) → ((j : J) → P j (g x j)) [Y x ↦ f₀ x])
    ( product-lift-is-LARI-family g₀ f₀ g)
    ( f))
  :=
  equiv-extensions-equiv extext 2 Δ¹ ∂Δ¹
  ( \ _ → (j : J) → (x : X) → P j (g x j) [Y x ↦ f₀ x j])
  ( \ _ → (x : X) → ((j : J) → P j (g x j)) [Y x ↦ f₀ x])
  ( \ _ → flip-ext-fun-inv I X Y
    ( J)
    ( \ x j → P j (g x j))
    ( \ (y : Y) (j : J) → f₀ y j))
  ( \ t → recOR(
      t ≡ 0₂ ↦ (\ (j : J) (x : I | X x) → product-lift-is-LARI-family g₀ f₀ g x j)
    , t ≡ 1₂ ↦ (\ (j : J) (x : I | X x) → f x j)))

#def is-contr-hom-flipped-product-lift uses (is-LARI-family-P weakfunext extext)
  ( g₀ : Y → ((j : J) → B j))
  ( f₀ : (y : Y) → (j : J) → P j (g₀ y j))
  ( g : (x : X) → ((j : J) → B j) [Y x ↦ g₀ x])
  ( f : (x : X) → ((j : J) → P j (g x j)) [Y x ↦ f₀ x])
  : is-contr (hom
    ( (x : X) → ((j : J) → P j (g x j)) [Y x ↦ f₀ x])
    ( product-lift-is-LARI-family g₀ f₀ g)
    ( f))
  :=
  is-contr-is-equiv-is-contr
  ( hom
    ( (j : J) → (x : X) → P j (g x j) [Y x ↦ f₀ x j])
    ( \ j x → product-lift-is-LARI-family g₀ f₀ g x j)
    ( \ j x → f x j))
  ( hom
    ( (x : X) → ((j : J) → P j (g x j)) [Y x ↦ f₀ x])
    ( product-lift-is-LARI-family g₀ f₀ g)
    ( f))
  ( equiv-hom-flipped-product-lift g₀ f₀ g f)
  ( is-contr-hom-product-lift g₀ f₀ g f)

```

```rzk title="BW23, Proposition 3.2.5"
#def is-LARI-family-product-is-LARI-family
  uses (is-LARI-family-P weakfunext extext)
  : is-LARI-family ((j : J) → B j) (\ bs → ((j : J) → (P j (bs j))))
  :=
  \ (g₀ : Y → ((j : J) → B j))
  ( f₀ : (y : Y) → (j : J) → P j (g₀ y j))
  ( g : (x : X) → ((j : J) → B j) [Y x ↦ g₀ x])
  → ( product-lift-is-LARI-family g₀ f₀ g
    , is-contr-hom-flipped-product-lift g₀ f₀ g)
```

```rzkk title="BW23, Proposition 3.2.5"
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
