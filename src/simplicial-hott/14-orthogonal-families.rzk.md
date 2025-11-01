# Orthogonal families

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

TODO

```rzk
#assume extext : ExtExt
```

## Definition of orthogonal families

```rzk
#def is-right-orthogonal-family
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( φ : ψ → TOPE)
  ( A : U)
  ( C : A → U)
  : U
  :=
    ( a : ψ → A)
  → ( f : (t : φ) → C (a t))
  → is-contr ((t : ψ) → C (a t) [φ t ↦ f t])
```

## Equivalence to `is-right-orthogonal-to-shape`

```rzk
#section has-contr-relative-extension-types-iff-is-right-orthogonal-family

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variable A : U
#variable C : A → U

#def has-contr-relative-extension-types-is-right-orthogonal-family
  ( is-right-orthogonal-family-C : is-right-orthogonal-family I ψ ϕ A C)
  : has-contr-relative-extension-types I ψ ϕ
    ( \ _ → total-type A C)
    ( \ _ → A)
    ( \ _ → projection-total-type A C)
  :=
  \ a τ →
  is-contr-equiv-is-contr'
  ( relative-extension-type I ψ ϕ
    ( \ _ → total-type A C)
    ( \ _ → A)
    ( \ _ → projection-total-type A C)
    ( a) (τ))
  ( (t : ψ) → C (τ t) [ϕ t ↦ second (a t)])
  ( equiv-relative-extension-type-direct-extension extext I ψ ϕ
    ( \ _ → A) ( \ _ → C) (a) (τ))
  ( is-right-orthogonal-family-C τ (\ t → second (a t)))

#def is-right-orthogonal-family-has-contr-relative-extension-types
  ( has-contr-rel-ext
  : has-contr-relative-extension-types I ψ ϕ
    ( \ _ → total-type A C)
    ( \ _ → A)
    ( \ _ → projection-total-type A C))
  : is-right-orthogonal-family I ψ ϕ A C
  :=
  \ a f →
  is-contr-equiv-is-contr
  ( relative-extension-type I ψ ϕ
    ( \ _ → total-type A C)
    ( \ _ → A)
    ( \ _ → projection-total-type A C)
    (\ t → (a t, f t)) (a))
  ( (t : ψ) → C (a t) [ϕ t ↦ f t])
  ( equiv-relative-extension-type-direct-extension extext I ψ ϕ
    ( \ _ → A) (\ _ → C) (\ t → (a t, f t)) (a))
  ( has-contr-rel-ext (\ t → (a t, f t)) a)

#end has-contr-relative-extension-types-iff-is-right-orthogonal-family
```

```rzk
#section is-right-orthogonal-family-iff-is-right-orthogonal-to-shape

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variable A : U
#variable C : A → U

#def is-right-orthogonal-to-shape-is-right-orthogonal-family
  ( is-right-orthogonal-family-C : is-right-orthogonal-family I ψ ϕ A C)
  : is-right-orthogonal-to-shape I ψ ϕ
    ( total-type A C)
    ( A)
    ( projection-total-type A C)
  :=
  is-right-orthogonal-to-shape-has-contr-relative-extension-types extext I ψ ϕ
  ( total-type A C)
  ( A)
  ( projection-total-type A C)
  ( has-contr-relative-extension-types-is-right-orthogonal-family I ψ ϕ A C
    ( is-right-orthogonal-family-C))

#def is-right-orthogonal-family-is-right-orthogonal-to-shape
  ( is-right-orth-C : is-right-orthogonal-to-shape I ψ ϕ
    ( total-type A C)
    ( A)
    ( projection-total-type A C))
  : is-right-orthogonal-family I ψ ϕ A C
  :=
  is-right-orthogonal-family-has-contr-relative-extension-types I ψ ϕ A C
  ( has-contr-relative-extension-types-is-right-orthogonal-to-shape
    ( extext) I ψ ϕ
    ( total-type A C)
    ( A)
    ( projection-total-type A C)
    ( is-right-orth-C))

#end is-right-orthogonal-family-iff-is-right-orthogonal-to-shape
```

## Leibniz cotensor map

```rzk
#def leibniz-cotensor-codomain
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( E B : U)
  ( p : E → B)
  : U
  :=
  Σ (f : Y → E)
  , Σ (g : X → B)
    , (\ (y : Y) → p (f y)) =_{ Y → B } (\ (y : Y) → g y)

#def leibniz-cotensor
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( E B : U)
  ( p : E → B)
  ( f : X → E)
  : leibniz-cotensor-codomain I X Y E B p
  := (\ (y : Y) → f y , (\ (x : X) → p (f x), refl))
```

```rzk
#def is-equiv-leibniz-cotensor-is-right-orthogonal-to-shape
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( E B : U)
  ( p : E → B)
  ( is-right-orthogonal-to-shape-p : is-right-orthogonal-to-shape I X Y E B p)
  : is-equiv
    ( X → E)
    ( leibniz-cotensor-codomain I X Y E B p)
    ( leibniz-cotensor I X Y E B p)
  :=
  second
  ( equiv-triple-comp
    ( X → E)
    ( Σ (f : Y → E) , (x : X) → E [Y x ↦ f x])
    ( Σ (f : Y → E) , (x : X) → B [Y x ↦ p (f x)])
    ( leibniz-cotensor-codomain I X Y E B p)
    ( equiv-extension-subshape I X Y E)
    ( total-equiv-family-of-equiv
      ( Y → E)
      ( \ f → (x : X) → E [Y x ↦ f x])
      ( \ f → (x : X) → B [Y x ↦ p (f x)])
      ( \ f → (\ F x → p (F x), is-right-orthogonal-to-shape-p f)))
    ( total-equiv-family-of-equiv
      ( Y → E)
      ( \ f → (x : X) → B [Y x ↦ p (f x)])
      ( \ f → Σ (g : X → B) , (\ y → p (f y)) =_{Y → B} (\ y → g y))
      ( \ f → inv-equiv
        ( Σ (g : X → B) , (\ y → p (f y)) =_{Y → B} (\ y → g y))
        ( (x : X) → B [Y x ↦ p (f x)])
        ( equiv-extension-homotopy-constraint I X Y B (\ y → p (f y))))))
```

```rzk
#def is-equiv-leibniz-cotensor-is-right-orthogonal-family uses (extext)
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( B : U)
  ( P : B → U)
  ( is-right-orthogonal-family-P : is-right-orthogonal-family I X Y B P)
  : is-equiv
  ( X → total-type B P)
  ( leibniz-cotensor-codomain I X Y (total-type B P) B
    ( projection-total-type B P))
  ( leibniz-cotensor I X Y (total-type B P) B
    ( projection-total-type B P))
  :=
  is-equiv-leibniz-cotensor-is-right-orthogonal-to-shape I X Y
  ( total-type B P) (B)
  ( projection-total-type B P)
  ( is-right-orthogonal-to-shape-is-right-orthogonal-family I X Y B P
    ( is-right-orthogonal-family-P))
```

## Inner families

```rzk
#def is-inner-family
  ( A : U)
  ( B : A → U)
  : U
  := is-right-orthogonal-family (2 × 2) Δ² Λ²₁ A B
```

```rzk
#def is-segal-fiber-is-inner-family
  ( B : U)
  ( P : B → U)
  ( is-inner-family-P : is-inner-family B P)
  ( b : B)
  : is-segal (P b)
  :=
  \ x y z f g → is-contr-equiv-is-contr
  ( ((t, s) : Δ²) → P b [s ≡ 0₂ ↦ f t, t ≡ 1₂ ↦ g s])
  ( Σ (h : hom (P b) x z) , (hom2 (P b) x y z f g h))
  ( \ τ → (\ t → τ (t, t), (\ ts → τ ts))
  , ( ( \ (_, τ) ts → τ ts, \ _ → refl)
    , ( \ (_, τ) ts → τ ts, \ _ → refl)))
  ( is-inner-family-P
    ( \ _ → b)
    ( \ (t, s) → recOR(s ≡ 0₂ ↦ f t, t ≡ 1₂ ↦ g s)))
```

## Isoinner families

```rzk
#def Iso-arr
  ( A : U)
  ( is-segal-A : is-segal A)
  : U
  := Σ (f : arr A) , is-iso-arrow A is-segal-A (f 0₂) (f 1₂) f

#def iso-arr-eq
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( p : x = y)
  : Iso-arr A is-segal-A
  := ( hom-eq A x y p, is-iso-arrow-hom-eq A is-segal-A x y p)
```

```rzk
#def is-isoinner-family
  ( B : U)
  ( P : B → U)
  : U
  :=
  Σ ( is-inner-family-P : is-inner-family B P)
  , ( (b : B)
    → (f : Iso-arr (P b)
           ( is-segal-fiber-is-inner-family B P is-inner-family-P b))
    → is-contr (Σ (e : P b)
      , f = iso-arr-eq (P b)
            ( is-segal-fiber-is-inner-family B P is-inner-family-P b)
            ( e) (e) (refl)))
```

