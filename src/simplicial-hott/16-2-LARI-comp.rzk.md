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

#def comp-lift-1-is-LARI-family
  ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  : (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)]
  := \ x → π₁ (is-LARI-family-P g (\ y → π₁ (f₀ y))) x

#def raw-comp-lift-is-LARI-family
  ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  ( f : (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
  : has-initial ((x : X) → Q (g x) (f x) [Y x ↦ π₂ (f₀ x)])
  :=
  is-LARI-family-Q
  ( \ x → (g x, f x))
  ( \ y → π₂ (f₀ y))

#def raw-comp-lift-2-is-LARI-family
  ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  : has-initial ((x : X) → Q (g x) (comp-lift-1-is-LARI-family g f₀ x) [Y x ↦ π₂ (f₀ x)])
  := raw-comp-lift-is-LARI-family g f₀ (comp-lift-1-is-LARI-family g f₀)

#def comp-lift-2-is-LARI-family
  ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  : (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ f₀ x]
  :=
  \ x → (comp-lift-1-is-LARI-family g f₀ x
  , π₁ (raw-comp-lift-2-is-LARI-family g f₀) x)

#def center-comp-lift-is-LARI-family
  ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  ( f : (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ f₀ x])
  : hom
  ( (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ f₀ x])
  ( comp-lift-2-is-LARI-family g f₀)
  ( f)
  :=
  \ t x → ((π₁ (π₂ (is-LARI-family-P g (\ y → π₁ (f₀ y))) (\ x → π₁ (f x))) t x)
  , π₁ (π₂ (raw-comp-lift-2-is-LARI-family g f₀) (\ x → π₂ (f x))) t x)

#def is-LARI-family-comp uses (is-LARI-family-Q is-LARI-family-P)
  : is-LARI-family I X Y B (\ b → Σ (p : P b) , Q b p)
  :=
  \ ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  → ( comp-lift-2-is-LARI-family g f₀
    , \ f → TODO (is-contr (hom
      ( (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ f₀ x])
      ( comp-lift-2-is-LARI-family g f₀)
      ( f))))







#end is-LARI-family-comp
```
