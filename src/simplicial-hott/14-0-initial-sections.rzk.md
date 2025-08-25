# Initial sections

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzkk
#assume funext : FunExt
#assume extext : ExtExt
```

Not all proofs are done in this file:

```rzkk
#assume TODO : (A : U) → A
```

## find a place

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

#def initial-section
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
