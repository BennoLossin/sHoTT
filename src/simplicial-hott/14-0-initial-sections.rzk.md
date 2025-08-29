# Initial sections

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
-- #assume funext : FunExt
#assume extext : ExtExt
```

Not all proofs are done in this file:

```rzkk
#assume TODO : (A : U) → A
```

## find a place

```rzk
#def dhom-ext-is-locally-contr-extext
  ( A : Δ¹ → U)
  ( is-contr-A : (t : Δ¹) → is-contr (A t))
  ( x : A 0₂)
  ( y : A 1₂)
  : (t : Δ¹) → A t [t ≡ 0₂ ↦ x, t ≡ 1₂ ↦ y]
  :=
  center-contraction
  ( (t : Δ¹) → A t [t ≡ 0₂ ↦ x, t ≡ 1₂ ↦ y])
  ( weakextext-extext extext 2 Δ¹ ∂Δ¹ A is-contr-A
    ( \ t → recOR(t ≡ 0₂ ↦ x, t ≡ 1₂ ↦ y)))
```

```rzk
#def is-iso-arrow-nat-trans-is-iso-arrow-boundary-type
  : U
  :=
    ( A : U)
  → ( is-rezk-A : is-rezk A)
  → ( x₁ : A) → (y₁ : A)
  → ( x₂ : A) → (y₂ : A)
  → ( f : hom A x₁ y₁) → ( g : hom A x₂ y₂)
  → ( α : (t : Δ¹) → hom A (f t) (g t))
  → ( is-iso-α-0 : is-iso-arrow A (π₁ is-rezk-A) x₁ x₂ (α 0₂))
  → ( is-iso-α-1 : is-iso-arrow A (π₁ is-rezk-A) y₁ y₂ (α 1₂))
  → ( ( t : Δ¹) → is-iso-arrow A (π₁ is-rezk-A) (f t) (g t) (α t)
    [t ≡ 0₂ ↦ is-iso-α-0, t ≡ 1₂ ↦ is-iso-α-1])

{-
#def is-iso-arrow-nat-trans-is-iso-arrow-boundary
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x₁ y₁ : A)
  ( x₂ y₂ : A)
  ( f : hom A x₁ y₁)
  ( g : hom A x₂ y₂)
  ( α : (t : Δ¹) → hom A (f t) (g t))
  ( has-iso-arrows-α : (t : Δ¹) → is-iso-arrow A is-segal-A (f t) (g t) (α t))
  ( is-iso-α-0 : is-iso-arrow A is-segal-A x₁ x₂ (α 0₂))
  ( is-iso-α-1 : is-iso-arrow A is-segal-A y₁ y₂ (α 1₂))
  : ( t : Δ¹) → is-iso-arrow A is-segal-A (f t) (g t) (α t)
    [t ≡ 0₂ ↦ is-iso-α-0, t ≡ 1₂ ↦ is-iso-α-1]
  :=
  dhom-ext-is-locally-contr-extext
  ( \ t → is-iso-arrow A is-segal-A (f t) (g t) (α t))
  ( \ t → is-contr-is-inhabited-is-prop
    ( is-iso-arrow A is-segal-A (f t) (g t) (α t))
    ( is-prop-is-iso-arrow extext A is-segal-A (f t) (g t) (α t))
    ( has-iso-arrows-α t))
  ( is-iso-α-0)
  ( is-iso-α-1)
-}

-- #assume is-iso-arrow-nat-trans-is-iso-arrow-boundary : is-iso-arrow-nat-trans-is-iso-arrow-boundary-type
```

## Definition

```rzk
#section initial-sections

#variable A : U
#variable B : A → U

#def is-initial-section
  ( s : (a : A) → B a)
  : U
  := (x : A) → is-initial (B x) (s x)

#def has-initial-section
  : U
  := Σ (s : (a : A) → B a) , is-initial-section s
```

We later want to show that this defines a LARI family. For the proof of this,
we need an a priori more powerful definition.

## Dependent initial sections

```rzk
#def is-dhom-initial-section
  ( s : (a : A) → B a)
  : U
  := (x : A) → (y : A) → (Y : B y) → (f : hom A x y)
  → is-contr (dhom A x y f B (s x) Y)

#def dhom-initial-section
  : U
  := Σ (s : (a : A) → B a) , is-dhom-initial-section s
```

We will now show that these are actually the same. The first direction is
simple:

```rzk
#def is-initial-section-is-dhom-initial-section
  ( s : (a : A) → B a)
  ( is-dhom-initial-section-s : is-dhom-initial-section s)
  : is-initial-section s
  :=
  \ (x : A) (X : B x) → is-contr-equiv-is-contr
  ( dhom A x x (id-hom A x) B (s x) X)
  ( hom (B x) (s x) X)
  ( equiv-hom-dhom A x B (s x) X)
  ( is-dhom-initial-section-s x x X (id-hom A x))

#end initial-sections
```

## Equivalences and Initial Sections

```rzk
#def has-initial-section-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : has-initial-section B (fib A B f)
  :=
  ( \ b → center-contraction (fib A B f b)
    ( is-contr-map-is-equiv A B f is-equiv-f b)
  , \ b → is-contr-hom-is-contr extext (fib A B f b)
    ( is-contr-map-is-equiv A B f is-equiv-f b)
    ( center-contraction (fib A B f b)
      ( is-contr-map-is-equiv A B f is-equiv-f b)))



```
