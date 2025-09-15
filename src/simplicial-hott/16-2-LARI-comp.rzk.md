# Composition of LARI families

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#assume TODO : (A : U) → A
```

```rzk
#section is-LARI-family-comp

#variable I : CUBE
#variable X : I → TOPE
#variable Y : X → TOPE
#variable B : U
#variable P : B → U
#variable Q : (b : B) → P b → U
#variable is-LARI-family-P : is-LARI-family I X Y B P
#variable is-LARI-family-Q : is-LARI-family I X Y (total-type B P) (\ (b, p) → Q b p)

#def comp-lift-is-LARI-family
  ( g₀ : Y → B)
  ( f₀ : (y : Y) → Σ (p : P (g₀ y)) , Q (g₀ y) p)
  ( g : (x : X) → B [Y x ↦ g₀ x])
  : (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ f₀ x]
  :=
  \ x → (π₁ (is-LARI-family-P g₀ (\ y → π₁ (f₀ y)) g) x
  , π₁ (is-LARI-family-Q
    ( \ y → (g₀ y, π₁ (f₀ y)))
    ( \ y → π₂ (f₀ y))
    ( \ x → (g x, π₁ (is-LARI-family-P g₀ (\ y → π₁ (f₀ y)) g) x))) x)

#def center-comp-lift-is-LARI-family
  ( g₀ : Y → B)
  ( f₀ : (y : Y) → Σ (p : P (g₀ y)) , Q (g₀ y) p)
  ( g : (x : X) → B [Y x ↦ g₀ x])
  ( f : (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ f₀ x])
  : hom
  ( (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ f₀ x])
  ( comp-lift-is-LARI-family g₀ f₀ g)
  ( f)
  :=
  \ t x → ((π₁ (π₂ (is-LARI-family-P g₀ (\ y → π₁ (f₀ y)) g) (\ x → π₁ (f x))) t x)
  , π₁ (π₂
    ( is-LARI-family-Q
      ( \ y → (g₀ y, π₁ (f₀ y)))
      ( \ y → π₂ (f₀ y))
      ( \ x → (g x, π₁ (is-LARI-family-P g₀ (\ y → π₁ (f₀ y)) g) x)))
    ( \ x → π₂ (f x))) t x)


#def is-LARI-family-comp uses (is-LARI-family-Q is-LARI-family-P)
  : is-LARI-family I X Y B (\ b → Σ (p : P b) , Q b p)
  :=
  \ (g₀ : Y → B)
  ( f₀ : (y : Y) → Σ (p : P (g₀ y)) , Q (g₀ y) p)
  ( g : (x : X) → B [Y x ↦ g₀ x])
  → ( comp-lift-is-LARI-family g₀ f₀ g
    , \ f → TODO (is-contr (hom
      ( (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ f₀ x])
      ( comp-lift-is-LARI-family g₀ f₀ g)
      ( f))))








#end is-LARI-family-comp
```
