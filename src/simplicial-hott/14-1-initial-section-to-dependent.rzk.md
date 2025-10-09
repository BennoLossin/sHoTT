# Initial sections are dependent initial sections

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Proof

The second one requires a bit more work:

```rzk
#section is-dhom-initial-section-is-initial-section

#variable A : U
#variable B : A → U
#variable is-inner-family-B : is-inner-family A B
#variable s : (a : A) → B a
#variable is-initial-section-s : is-initial-section A B s

#def ctr
  (a : A)
  (b : B a)
  : hom (B a) (s a) b
  := center-contraction (hom (B a) (s a) b) (is-initial-section-s a b)

#def fff uses (is-initial-section-s)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  : ((t₁, t₂) : Λ²₁) → B (f t₁)
  := \ (t₁, t₂) → recOR(t₂ ≡ 0₂ ↦ s (f t₁), t₁ ≡ 1₂ ↦ ctr y Y t₂)

#def C uses (is-initial-section-s s)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  : (t : Δ²) → B (f (π₁ t)) [Λ²₁ t ↦ fff x y Y f t]
  :=
  lift-is-inner-family A B is-inner-family-B
  ( \ (t : Δ²) → f (π₁ t))
  ( fff x y Y f)

#def c uses (is-initial-section-s s is-inner-family-B)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  : dhom A x y f B (s x) Y
  := \ t → C x y Y f (t, t)

#def F-square
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  ( F : dhom A x y f B (s x) Y)
  : ((t₁, t₂) : 2 × 2) → B (f t₁) [t₂ ≡ 0₂ ↦ s (f t₁), t₂ ≡ 1₂ ↦ F (t₁)]
  :=
  \ (t₁, t₂) → center-contraction
  ( hom (B (f t₁)) (s (f t₁)) (F t₁))
  ( is-initial-section-s (f t₁) (F t₁))
  ( t₂)

#def diag-F-square uses (is-initial-section-s)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  ( F : dhom A x y f B (s x) Y)
  : dhom A x y f B (s x) Y
  := \ t → F-square x y Y f F (t, t)

#def FFF uses (is-initial-section-s)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  ( F : dhom A x y f B (s x) Y)
  : ((t₁, t₂) : Λ²₁) → B (f t₂)
  := \ (t₁, t₂) → recOR(t₂ ≡ 0₂ ↦ ctr x (s x) t₁, t₁ ≡ 1₂ ↦ F t₂)

#def lower-triag-F uses (is-initial-section-s)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  ( F : dhom A x y f B (s x) Y)
  : (t : Δ²) → B (f (π₂ t)) [Λ²₁ t ↦ FFF x y Y f F t]
  := \ (t₁, t₂) → F-square x y Y f F (t₂, t₁)

#def C' uses (is-initial-section-s s)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  ( F : dhom A x y f B (s x) Y)
  : (t : Δ²) → B (f (π₂ t)) [Λ²₁ t ↦ FFF x y Y f F t]
  :=
  lift-is-inner-family A B is-inner-family-B
  ( \ (t : Δ²) → f (π₂ t))
  ( FFF x y Y f F)

#def xgcstie
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  ( F : dhom A x y f B (s x) Y)
  : (t : Δ²) → B (f (π₂ t)) [Λ²₁ t ↦ FFF x y Y f F t]
  :=
  transport
  ( hom (B x) (s x) (s x))
  ( \ g → ((t : Δ²) → B (f (π₂ t)) [Λ²₁ t ↦ recOR(π₂ t ≡ 0₂ ↦ g (π₁ t), π₁ t ≡ 1₂ ↦ F (π₂ t))]))
  ( id-hom (B x) (s x))
  ( ctr x (s x))
  ( rev (hom (B x) (s x) (s x))
    ( ctr x (s x))
    ( id-hom (B x) (s x))
    ( homotopy-contraction (hom (B x) (s x) (s x))
      ( is-initial-section-s x (s x))
      ( id-hom (B x) (s x))))
  ( \ (t₁, t₂) → F t₂)

#def F-eq-diag-xgcstie uses (is-initial-section-s)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  ( F : dhom A x y f B (s x) Y)
  : F =_{dhom A x y f B (s x) Y} (\ (t : Δ¹) → xgcstie x y Y f F (t, t))
  :=
  ap
  ( Σ (g : hom (B x) (s x) (s x))
    , ( (t : Δ²) → B (f (π₂ t))
        [ Λ²₁ t ↦ recOR(π₂ t ≡ 0₂ ↦ g (π₁ t), π₁ t ≡ 1₂ ↦ F (π₂ t))]))
  ( dhom A x y f B (s x) Y)
  ( id-hom (B x) (s x), \ (t₁, t₂) → F t₂)
  ( ctr x (s x), xgcstie x y Y f F)
  ( \ (g, D) t → D (t, t))
  ( transport-lift
    ( hom (B x) (s x) (s x))
    ( \ g → ((t : Δ²) → B (f (π₂ t)) [Λ²₁ t ↦ recOR(π₂ t ≡ 0₂ ↦ g (π₁ t), π₁ t ≡ 1₂ ↦ F (π₂ t))]))
    ( id-hom (B x) (s x))
    ( ctr x (s x))
    ( rev (hom (B x) (s x) (s x))
      ( ctr x (s x))
      ( id-hom (B x) (s x))
      ( homotopy-contraction (hom (B x) (s x) (s x))
        ( is-initial-section-s x (s x))
        ( id-hom (B x) (s x))))
    ( \ (t₁, t₂) → F t₂))

#def mtpie'' uses (is-initial-section-s)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  ( F : dhom A x y f B (s x) Y)
  : C' x y Y f F = xgcstie x y Y f F
  :=
  is-unique-lift-is-inner-family A B is-inner-family-B
  ( \ (t : Δ²) → f (π₂ t))
  ( FFF x y Y f F)
  ( xgcstie x y Y f F)

#def mtpie' uses (is-initial-section-s)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  ( F : dhom A x y f B (s x) Y)
  : C' x y Y f F = lower-triag-F x y Y f F
  :=
  is-unique-lift-is-inner-family A B is-inner-family-B
  ( \ (t : Δ²) → f (π₂ t))
  ( FFF x y Y f F)
  ( lower-triag-F x y Y f F)

#def diag-F-square-eq-F
  uses (is-initial-section-s s is-inner-family-B)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  ( F : dhom A x y f B (s x) Y)
  : diag-F-square x y Y f F = F
  :=
  concat
  ( dhom A x y f B (s x) Y)
  ( diag-F-square x y Y f F)
  ( \ t → xgcstie x y Y f F (t, t))
  ( F)
  ( ap
    ( (t : Δ²) → B (f (π₂ t)) [Λ²₁ t ↦ FFF x y Y f F t])
    ( dhom A x y f B (s x) Y)
    ( lower-triag-F x y Y f F)
    ( xgcstie x y Y f F)
    ( \ D t → D (t, t))
    ( concat
      ( (t : Δ²) → B (f (π₂ t)) [Λ²₁ t ↦ FFF x y Y f F t])
      ( lower-triag-F x y Y f F)
      ( C' x y Y f F)
      ( xgcstie x y Y f F)
      ( rev
        ( (t : Δ²) → B (f (π₂ t)) [Λ²₁ t ↦ FFF x y Y f F t])
        ( C' x y Y f F)
        ( lower-triag-F x y Y f F)
        (mtpie' x y Y f F))
      ( mtpie'' x y Y f F)))
  ( rev
    ( dhom A x y f B (s x) Y)
    ( F)
    ( \ t → xgcstie x y Y f F (t, t))
    ( F-eq-diag-xgcstie x y Y f F))

#def upper-triag-F uses (is-initial-section-s)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  ( F : dhom A x y f B (s x) Y)
  : (t : Δ²) → B (f (π₁ t)) [Λ²₁ t ↦ fff x y Y f t]
  := \ t → F-square x y Y f F t

#def mtpie uses (is-initial-section-s)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  ( F : dhom A x y f B (s x) Y)
  : C x y Y f = upper-triag-F x y Y f F
  :=
  is-unique-lift-is-inner-family A B is-inner-family-B
  ( \ (t : Δ²) → f (π₁ t))
  ( fff x y Y f)
  ( upper-triag-F x y Y f F)

#def c-eq-diag-F-square uses (is-initial-section-s is-inner-family-B)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  ( F : dhom A x y f B (s x) Y)
  : c x y Y f = diag-F-square x y Y f F
  :=
  ap
  ( (t : Δ²) → B (f (π₁ t)) [Λ²₁ t ↦ fff x y Y f t])
  ( dhom A x y f B (s x) Y)
  ( C x y Y f)
  ( upper-triag-F x y Y f F)
  ( \ D t → D (t, t))
  ( mtpie x y Y f F)

#def tmp uses (is-initial-section-s s is-inner-family-B)
  ( x y : A)
  ( Y : B y)
  ( f : hom A x y)
  : is-contr (dhom A x y f B (s x) Y)
  :=
  ( c x y Y f
  , \ F → concat
    ( dhom A x y f B (s x) Y)
    ( c x y Y f)
    ( diag-F-square x y Y f F)
    ( F)
    ( c-eq-diag-F-square x y Y f F)
    ( diag-F-square-eq-F x y Y f F))

#def is-dhom-initial-section-is-initial-section
  uses (is-initial-section-s s is-inner-family-B)
  : is-dhom-initial-section A B s
  := tmp

#end is-dhom-initial-section-is-initial-section
```

```rzk
#def has-dhom-initial-has-initial-is-inner-family
  ( A : U)
  ( B : A → U)
  ( has-initial-B : (a : A) → has-initial (B a))
  ( is-inner-family-B : is-inner-family A B)
  : (a : A) → has-dhom-initial A B a
  :=
  \ a → (π₁ (has-initial-B a)
  , tmp A B is-inner-family-B
    ( \ a → π₁ (has-initial-B a))
    ( \ a → π₂ (has-initial-B a))
    ( a))
```

```rzk
#def is-dhom-initial-has-initial-is-inner-family
  ( A : U)
  ( B : A → U)
  ( has-initial-B : (a : A) → has-initial (B a))
  ( is-inner-family-B : is-inner-family A B)
  : (a : A) → is-dhom-initial A B a (π₁ (has-initial-B a))
  :=
  \ a → tmp A B is-inner-family-B
  ( \ a → π₁ (has-initial-B a))
  ( \ a → π₂ (has-initial-B a))
  ( a)
```
