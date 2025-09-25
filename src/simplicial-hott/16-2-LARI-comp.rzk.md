# Composition of LARI families

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#assume TODO : (A : U) → A
```

## Initial Objects in Sigma types

```rzk
#def has-initial-total-type-has-initial-fib-is-inner-fam
  ( B : U)
  ( P : B → U)
  ( is-inner-fib-type-fam-P : is-inner-fib-type-fam B P)
  ( has-initial-B : has-initial B)
  ( has-initial-P : (b : B) → has-initial (P b))
  : has-initial (total-type B P)
  :=
  ( (π₁ has-initial-B, π₁ (has-initial-P (π₁ has-initial-B)))
  , \ (b, p) → is-contr-equiv-is-contr'
    ( hom
      ( total-type B P)
      ( π₁ has-initial-B, π₁ (has-initial-P (π₁ has-initial-B)))
      ( b, p))
    ( hom B (π₁ has-initial-B) (b))
    ( equiv-comp
      ( hom
        ( total-type B P)
        ( π₁ has-initial-B, π₁ (has-initial-P (π₁ has-initial-B)))
        ( b, p))
      ( Σ (h : hom B (π₁ has-initial-B) (b))
        , dhom B (π₁ has-initial-B) (b) h P (π₁ (has-initial-P (π₁ has-initial-B))) p)
      ( hom B (π₁ has-initial-B) (b))
      ( equiv-hom-sigma-dhom B P
        ( π₁ has-initial-B, π₁ (has-initial-P (π₁ has-initial-B)))
        ( b, p))
      ( equiv-total-type-is-contr
        ( hom B (π₁ has-initial-B) (b))
        ( \ h → dhom B (π₁ has-initial-B) (b) h P (π₁ (has-initial-P (π₁ has-initial-B))) p)
        ( is-dhom-initial-section-is-initial-section B P
          ( is-inner-fib-type-fam-P)
          ( \ b → π₁ (has-initial-P b))
          ( \ b → π₂ (has-initial-P b))
          ( π₁ has-initial-B)
          ( b)
          ( p))))
    ( π₂ has-initial-B b))
```


```rzk
#variable I : CUBE
#variable X : I → TOPE
#variable Y : X → TOPE
```

## Composing Liftings

```rzk
#def lift
  ( B : X → U)
  ( P : (x : X) → B x → U)
  ( g : (x : X) → B x)
  ( f₀ : (y : Y) → P y (g y))
  : U
  := (x : X) → P x (g x) [Y x ↦ f₀ x]
```

```rzk
#def equiv-lift-comp
  ( B : U)
  ( P : B → U)
  ( Q : (b : B) → P b → U)
  ( g : X → B)
  ( f₀ : (y : Y) → (Σ (p : P (g y)) , Q (g y) p))
  : Equiv
  ( lift (\ _ → B) (\ _ b → Σ (p : P b) , Q b p) (g) (f₀))
  ( Σ (l : lift (\ _ → B) (\ _ → P) (g) (\ y → π₁ (f₀ y)))
    , lift (\ _ → total-type B P) (\ _ (b, p) → Q b p) (\ x → (g x, l x)) (\ y →  π₂ (f₀ y)))
  :=
  equiv-is-inverse
  ( lift (\ _ → B) (\ _ b → Σ (p : P b) , Q b p) (g) (f₀))
  ( Σ (l : lift (\ _ → B) (\ _ → P) (g) (\ y → π₁ (f₀ y)))
    , lift (\ _ → total-type B P) (\ _ (b, p) → Q b p) (\ x → (g x, l x)) (\ y →  π₂ (f₀ y)))
  ( \ l → (\ x → π₁ (l x), \ x → π₂ (l x)))
  ( \ (l₁, l₂) x → (l₁ x, l₂ x))
  ( \ _ → refl)
  ( \ _ → refl)
```

## ...

```rzk
#section is-LARI-family-comp

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

#def raw-comp-lift-2-is-LARI-family uses (is-LARI-family-P is-LARI-family-Q)
  ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  : has-initial ((x : X) → Q (g x) (comp-lift-1-is-LARI-family g f₀ x) [Y x ↦ π₂ (f₀ x)])
  := raw-comp-lift-is-LARI-family g f₀ (comp-lift-1-is-LARI-family g f₀)

#def comp-lift-2-is-LARI-family uses (is-LARI-family-P is-LARI-family-Q)
  ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  : (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ f₀ x]
  :=
  \ x → (comp-lift-1-is-LARI-family g f₀ x
  , π₁ (raw-comp-lift-2-is-LARI-family g f₀) x)

#def helper1
  ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  ( f : (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
  : is-contr (hom
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( comp-lift-1-is-LARI-family g f₀)
    ( f))
  := π₂ (is-LARI-family-P g (\ y → π₁ (f₀ y))) f

#def helper2 uses (is-LARI-family-P is-LARI-family-Q)
  ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  ( f : (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
  ( F : (x : X) → Q (g x) (f x) [Y x ↦ π₂ (f₀ x)])
  ( h : hom
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( comp-lift-1-is-LARI-family g f₀)
    ( f))
  : is-contr (dhom
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( comp-lift-1-is-LARI-family g f₀)
    ( f)
    ( h)
    ( \ f → ((x : X) → Q (g x) (f x) [Y x ↦ π₂ (f₀ x)]))
    ( \ x → π₁ (raw-comp-lift-2-is-LARI-family g f₀) x)
    ( F))
  :=
  is-dhom-initial-section-is-initial-section
  ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
  ( \ f → ((x : X) → Q (g x) (f x) [Y x ↦ π₂ (f₀ x)]))
  ( TODO (is-inner-fib-type-fam
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( \ f → ((x : X) → Q (g x) (f x) [Y x ↦ π₂ (f₀ x)]))))
  ( \ f x → π₁ (raw-comp-lift-is-LARI-family g f₀ f) x)
  ( \ f → π₂ (raw-comp-lift-is-LARI-family g f₀ f))
  ( comp-lift-1-is-LARI-family g f₀)
  ( f)
  ( F)
  ( h)

#def helper3 uses (is-LARI-family-P is-LARI-family-Q)
  ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  ( f : (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ (f₀ x)])
  : Equiv
  ( hom
    ( (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ (f₀ x)])
    ( comp-lift-2-is-LARI-family g f₀)
    ( f))
  ( Σ (h : hom
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( comp-lift-1-is-LARI-family g f₀)
    ( \ x → π₁ (f x)))
  , dhom
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( comp-lift-1-is-LARI-family g f₀)
    ( \ x → π₁ (f x))
    ( h)
    ( \ f → ((x : X) → Q (g x) (f x) [Y x ↦ π₂ (f₀ x)]))
    ( \ x → π₁ (raw-comp-lift-2-is-LARI-family g f₀) x)
    ( \ x → π₂ (f x)))
  :=
  TODO (Equiv
  ( hom
    ( (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ (f₀ x)])
    ( comp-lift-2-is-LARI-family g f₀)
    ( f))
  ( Σ (h : hom
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( comp-lift-1-is-LARI-family g f₀)
    ( \ x → π₁ (f x)))
  , dhom
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( comp-lift-1-is-LARI-family g f₀)
    ( \ x → π₁ (f x))
    ( h)
    ( \ f → ((x : X) → Q (g x) (f x) [Y x ↦ π₂ (f₀ x)]))
    ( \ x → π₁ (raw-comp-lift-2-is-LARI-family g f₀) x)
    ( \ x → π₂ (f x))))

#def helper4 uses (is-LARI-family-P is-LARI-family-Q TODO)
  ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  ( f : (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ (f₀ x)])
  : Equiv
  ( Σ (h : hom
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( comp-lift-1-is-LARI-family g f₀)
    ( \ x → π₁ (f x)))
  , dhom
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( comp-lift-1-is-LARI-family g f₀)
    ( \ x → π₁ (f x))
    ( h)
    ( \ f → ((x : X) → Q (g x) (f x) [Y x ↦ π₂ (f₀ x)]))
    ( \ x → π₁ (raw-comp-lift-2-is-LARI-family g f₀) x)
    ( \ x → π₂ (f x)))
  ( hom
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( comp-lift-1-is-LARI-family g f₀)
    ( \ x → π₁ (f x)))
  :=
  equiv-total-type-is-contr
  ( hom
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( comp-lift-1-is-LARI-family g f₀)
    ( \ x → π₁ (f x)))
  ( \ h → dhom
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( comp-lift-1-is-LARI-family g f₀)
    ( \ x → π₁ (f x))
    ( h)
    ( \ f → ((x : X) → Q (g x) (f x) [Y x ↦ π₂ (f₀ x)]))
    ( \ x → π₁ (raw-comp-lift-2-is-LARI-family g f₀) x)
    ( \ x → π₂ (f x)))
  ( \ h → helper2 g f₀ (\ x → π₁ (f x)) (\ x → π₂ (f x)) h)

#def helper5 uses (is-LARI-family-P is-LARI-family-Q TODO)
  ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  ( f : (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ (f₀ x)])
  : is-contr (hom
    ( (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ (f₀ x)])
    ( comp-lift-2-is-LARI-family g f₀)
    ( f))
  :=
  is-contr-equiv-is-contr'
  ( hom
    ( (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ (f₀ x)])
    ( comp-lift-2-is-LARI-family g f₀)
    ( f))
  ( hom
    ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
    ( comp-lift-1-is-LARI-family g f₀)
    ( \ x → π₁ (f x)))
  ( equiv-comp
    ( hom
      ( (x : X) → (Σ (p : P (g x)) , Q (g x) p) [Y x ↦ (f₀ x)])
      ( comp-lift-2-is-LARI-family g f₀)
      ( f))
    ( Σ (h : hom
      ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
      ( comp-lift-1-is-LARI-family g f₀)
      ( \ x → π₁ (f x)))
    , dhom
      ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
      ( comp-lift-1-is-LARI-family g f₀)
      ( \ x → π₁ (f x))
      ( h)
      ( \ f → ((x : X) → Q (g x) (f x) [Y x ↦ π₂ (f₀ x)]))
      ( \ x → π₁ (raw-comp-lift-2-is-LARI-family g f₀) x)
      ( \ x → π₂ (f x)))
    ( hom
      ( (x : X) → P (g x) [Y x ↦ π₁ (f₀ x)])
      ( comp-lift-1-is-LARI-family g f₀)
      ( \ x → π₁ (f x)))
    ( helper3 g f₀ f)
    ( helper4 g f₀ f))
  ( helper1 g f₀ (\ x → π₁ (f x)))

#def is-LARI-family-comp uses (is-LARI-family-Q is-LARI-family-P TODO)
  : is-LARI-family I X Y B (\ b → Σ (p : P b) , Q b p)
  :=
  \ ( g : (x : X) → B)
  ( f₀ : (y : Y) → Σ (p : P (g y)) , Q (g y) p)
  → ( comp-lift-2-is-LARI-family g f₀
    , helper5 g f₀)

#end is-LARI-family-comp
```
