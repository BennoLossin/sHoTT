# Squares and Triangles

```rzk
#lang rzk-1
```

```rzk
#def square
  ( A : U)
  ( x y z w : A)
  ( f₁ : hom A x y)
  ( g₁ : hom A x z)
  ( f₂ : hom A z w)
  ( g₂ : hom A y w)
  : U
  :=
  ( (t, s) : 2 × 2) → A
  [ t ≡ 0₂ ↦ g₁ s
  , t ≡ 1₂ ↦ g₂ s
  , s ≡ 0₂ ↦ f₁ t
  , s ≡ 1₂ ↦ f₂ t]
```

```rzk
#def curried-square
  ( A : U)
  ( x y z w : A)
  ( f₁ : hom A x y)
  ( g₁ : hom A x z)
  ( f₂ : hom A z w)
  ( g₂ : hom A y w)
  : U
  :=
  (t : 2) → (s : 2) → A
  [ s ≡ 0₂ ↦ f₁ t
  , s ≡ 1₂ ↦ f₂ t
  , t ≡ 0₂ ↦ g₁ s
  , t ≡ 1₂ ↦ g₂ s]
```

```rzk
#def equiv-square-curried-square
  ( A : U)
  ( x y z w : A)
  ( f₁ : hom A x y)
  ( g₁ : hom A x z)
  ( f₂ : hom A z w)
  ( g₂ : hom A y w)
  : Equiv
    ( square A x y z w f₁ g₁ f₂ g₂)
    ( curried-square A x y z w f₁ g₁ f₂ g₂)
  :=
  equiv-is-inverse
  ( square A x y z w f₁ g₁ f₂ g₂)
  ( curried-square A x y z w f₁ g₁ f₂ g₂)
  ( \ σ t s → σ (t, s))
  ( \ σ (t, s) → σ t s)
  ( \ _ → refl)
  ( \ _ → refl)
```

```rzk
#def equiv-square-glued-triangles
  ( A : U)
  ( x y z w : A)
  ( f₁ : hom A x y)
  ( g₁ : hom A x z)
  ( f₂ : hom A z w)
  ( g₂ : hom A y w)
  : Equiv
    ( square A x y z w f₁ g₁ f₂ g₂)
    ( Σ (d : hom A x w)
      , product
        ( hom2 A x y w f₁ g₂ d)
        ( hom2 A x z w g₁ f₂ d))
  :=
  equiv-is-inverse
  ( square A x y z w f₁ g₁ f₂ g₂)
  ( Σ (d : hom A x w)
    , product
      ( hom2 A x y w f₁ g₂ d)
      ( hom2 A x z w g₁ f₂ d))
  ( \ σ → (\ t → σ (t, t) , ( \ tt → σ tt, \ (t, s) → σ (s, t))))
  ( \ (_, (τ₁, τ₂)) (t, s) → recOR
    ( s ≤ t ↦ τ₁ (t, s)
    , t ≤ s ↦ τ₂ (s, t)))
  (\ _ → refl)
  (\ _ → refl)

#def equiv-square-left-id-triangle-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y w : A)
  ( f₁ : hom A x y)
  ( f₂ : hom A x w)
  ( g₂ : hom A y w)
  : Equiv
    ( square A x y x w f₁ (id-hom A x) f₂ g₂)
    ( hom2 A x y w f₁ g₂ f₂)
  :=
  equiv-quadruple-comp
  ( square A x y x w f₁ (id-hom A x) f₂ g₂)
  ( Σ (d : hom A x w)
    , product
      ( hom2 A x y w f₁ g₂ d)
      ( hom2 A x x w (id-hom A x) f₂ d))
  ( Σ (d : hom A x w)
    , product
      ( hom2 A x y w f₁ g₂ d)
      ( f₂ = d))
  ( Σ (d : hom A x w)
    , product
      ( f₂ = d)
      ( hom2 A x y w f₁ g₂ d))
  ( hom2 A x y w f₁ g₂ f₂)
  ( equiv-square-glued-triangles A x y x w f₁ (id-hom A x) f₂ g₂)
  ( total-equiv-family-of-equiv
    ( hom A x w)
    ( \ d → product
      ( hom2 A x y w f₁ g₂ d)
      ( hom2 A x x w (id-hom A x) f₂ d))
    ( \ d → product
      ( hom2 A x y w f₁ g₂ d)
      ( f₂ = d))
    ( \ d → equiv-product-equivs
      ( hom2 A x y w f₁ g₂ d)
      ( hom2 A x y w f₁ g₂ d)
      ( identity (hom2 A x y w f₁ g₂ d), is-equiv-identity (hom2 A x y w f₁ g₂ d))
      ( hom2 A x x w (id-hom A x) f₂ d)
      ( f₂ = d)
      ( inv-equiv
        ( f₂ = d)
        ( hom2 A x x w (id-hom A x) f₂ d)
        ( equiv-homotopy-hom2-is-segal A is-segal-A x w f₂ d))))
  ( equiv-is-inverse
    ( Σ (d : hom A x w)
      , product
        ( hom2 A x y w f₁ g₂ d)
        ( f₂ = d))
    ( Σ (d : hom A x w)
      , product
        ( f₂ = d)
        ( hom2 A x y w f₁ g₂ d))
    ( \ (d, (τ, p)) → (d, (p, τ)))
    ( \ (d, (p, τ)) → (d, (τ, p)))
    ( \ _ → refl)
    ( \ _ → refl))
  ( equiv-based-paths-family (hom A x w) (\ d → hom2 A x y w f₁ g₂ d) f₂)

#def hom2-square-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y w : A)
  ( f₁ : hom A x y)
  ( f₂ : hom A x w)
  ( g₂ : hom A y w)
  : square A x y x w f₁ (id-hom A x) f₂ g₂ → hom2 A x y w f₁ g₂ f₂
  :=
  π₁ (equiv-square-left-id-triangle-is-segal A is-segal-A x y w f₁ f₂ g₂)

#def square-hom2
  ( A : U)
  ( x y w : A)
  ( f₁ : hom A x y)
  ( f₂ : hom A x w)
  ( g₂ : hom A y w)
  ( τ : hom2 A x y w f₁ g₂ f₂)
  : square A x y x w f₁ (id-hom A x) f₂ g₂
  :=
  \ (t, s) → recOR(s ≤ t ↦ τ (t, s), t ≤ s ↦ f₂ t)

#def equiv-square-sides-id-eq-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A x y)
  : Equiv
    ( square A x y x y f (id-hom A x) g (id-hom A y))
    ( f = g)
  :=
  equiv-comp
  ( square A x y x y f (id-hom A x) g (id-hom A y))
  ( hom2 A x y y f (id-hom A y) g)
  ( f = g)
  ( equiv-square-left-id-triangle-is-segal A is-segal-A x y y f g (id-hom A y))
  ( inv-equiv
    ( f = g)
    ( hom2 A x y y f (id-hom A y) g)
    ( equiv-homotopy-hom2'-is-segal A is-segal-A x y f g))

#def eq-square-id-hom-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A x y)
  ( σ : square A x y x y f (id-hom A x) g (id-hom A y))
  : f = g
  :=
  π₁
  ( equiv-square-sides-id-eq-is-segal A is-segal-A x y f g)
  ( σ)

#def square-id-hom-eq-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A x y)
  ( p : f = g)
  : square A x y x y f (id-hom A x) g (id-hom A y)
  :=
  π₁
  ( inv-equiv
    ( square A x y x y f (id-hom A x) g (id-hom A y))
    ( f = g)
    ( equiv-square-sides-id-eq-is-segal A is-segal-A x y f g))
  ( p)

#def ind-square-sides-id-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( C : (g : hom A x y) → (square A x y x y f (id-hom A x) g (id-hom A y)) → U)
  ( d : C f (\ (t, s) → f t))
  ( g : hom A x y)
  ( σ : square A x y x y f (id-hom A x) g (id-hom A y))
  : C g σ
  :=
  transport
  ( square A x y x y f (id-hom A x) g (id-hom A y))
  ( C g)
  ( square-id-hom-eq-is-segal A is-segal-A x y f g
    ( eq-square-id-hom-is-segal A is-segal-A x y f g σ))
  ( σ)
  ( inv-equiv-cancel
    ( square A x y x y f (id-hom A x) g (id-hom A y))
    ( f = g)
    ( equiv-square-sides-id-eq-is-segal A is-segal-A x y f g)
    ( σ))
  ( ind-path (hom A x y) f
    ( \ g p → C g (square-id-hom-eq-is-segal A is-segal-A x y f g p))
    ( d)
    ( g)
    ( eq-square-id-hom-is-segal A is-segal-A x y f g σ))

#def ind-curried-square-sides-id-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( C : (g : hom A x y) → (curried-square A x y x y f (id-hom A x) g (id-hom A y)) → U)
  ( d : C f (\ t _ → f t))
  ( g : hom A x y)
  ( σ : curried-square A x y x y f (id-hom A x) g (id-hom A y))
  : C g σ
  :=
  ind-square-sides-id-is-segal A is-segal-A x y f
  ( \ g σ → C g (\ t s → σ (t, s)))
  ( d)
  ( g)
  ( \ (t, s) → σ t s)

#def triangle-square-left-id-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y w : A)
  ( f₁ : hom A x y)
  ( f₂ : hom A x w)
  ( g₂ : hom A y w)
  ( σ : square A x y x w f₁ (id-hom A x) f₂ g₂)
  : hom2 A x y w f₁ g₂ f₂
  :=
  π₁ (equiv-square-left-id-triangle-is-segal A is-segal-A x y w f₁ f₂ g₂) σ
```

```rzk
#def is-contr-square-sides-eq-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z w : A)
  ( f : hom A x y)
  ( p : x = z)
  ( q : y = w)
  : is-contr
    ( Σ (g : hom A z w)
      , square A x y z w f (hom-eq A x z p) g (hom-eq A y w q))
  :=
  ind-path A x
  ( \ z p → is-contr
    ( Σ (g : hom A z w)
      , square A x y z w f (hom-eq A x z p) g (hom-eq A y w q)))
  ( ind-path A y
    ( \ w q → is-contr
      ( Σ (g : hom A x w)
        , square A x y x w f (id-hom A x) g (hom-eq A y w q)))
    ( is-contr-equiv-is-contr'
      ( Σ (g : hom A x y)
        , square A x y x y f (id-hom A x) g (id-hom A y))
      ( Σ (g : hom A x y) , f = g)
      ( total-equiv-family-of-equiv (hom A x y)
        ( \ g → square A x y x y f (id-hom A x) g (id-hom A y))
        ( \ g → f = g)
        ( \ g → equiv-square-sides-id-eq-is-segal A is-segal-A x y f g))
      ( is-contr-based-paths (hom A x y) f))
    ( w)
    ( q))
  ( z)
  ( p)
```

```rzk
#def is-contr-square-sides-iso-is-rezk
  ( A : U)
  ( is-rezk-A : is-rezk A)
  ( x y z w : A)
  ( f : hom A x y)
  ( p : Iso A (π₁ is-rezk-A) x z)
  ( q : Iso A (π₁ is-rezk-A) y w)
  : is-contr
    ( Σ (g : hom A z w)
      , square A x y z w f (π₁ p) g (π₁ q))
  :=
  iso-ind-is-rezk A is-rezk-A x
  ( \ z p → is-contr
    ( Σ (g : hom A z w)
      , square A x y z w f (π₁ p) g (π₁ q)))
  ( iso-ind-is-rezk A is-rezk-A y
    ( \ w q → is-contr
      ( Σ (g : hom A x w)
        , square A x y x w f (id-hom A x) g (π₁ q)))
    ( is-contr-square-sides-eq-is-segal A (π₁ is-rezk-A) x y x y
      ( f) (refl) (refl))
    ( w)
    ( q))
  ( z)
  ( p)
```

```rzk
#def iso-square-sides-iso-is-rezk
  ( A : U)
  ( is-rezk-A : is-rezk A)
  ( x₁ y₁ : A)
  ( x₂ y₂ : A)
  ( f : hom A x₁ y₁)
  ( g : hom A x₂ y₂)
  ( h : Iso A (π₁ is-rezk-A) x₁ x₂)
  ( k : Iso A (π₁ is-rezk-A) y₁ y₂)
  ( σ : square A x₁ y₁ x₂ y₂ f (π₁ h) g (π₁ k))
  : (t : Δ¹) → Iso A (π₁ is-rezk-A) (f t) (g t) [t ≡ 0₂ ↦ h, t ≡ 1₂ ↦ k]
  :=
  iso-ind-is-rezk A is-rezk-A x₁
  ( \ x₂ h → (g : hom A x₂ y₂)
    → ( σ : square A x₁ y₁ x₂ y₂ f (π₁ h) g (π₁ k))
    → ( (t : Δ¹) → Iso A (π₁ is-rezk-A) (f t) (g t) [t ≡ 0₂ ↦ h, t ≡ 1₂ ↦ k]))
  ( iso-ind-is-rezk A is-rezk-A y₁
    ( \ y₂ k → (g : hom A x₁ y₂)
      → ( σ : square A x₁ y₁ x₁ y₂ f (π₁ (iso-eq A (π₁ is-rezk-A) x₁ x₁ refl)) g (π₁ k))
      → ( (t : Δ¹) → Iso A (π₁ is-rezk-A) (f t) (g t) [t ≡ 0₂ ↦ iso-eq A (π₁ is-rezk-A) x₁ x₁ refl, t ≡ 1₂ ↦ k]))
    ( \ g σ → ind-path (hom A x₁ y₁) (f)
      ( \ g _ → (t : Δ¹) → Iso A (π₁ is-rezk-A) (f t) (g t)
        [ t ≡ 0₂ ↦ iso-eq A (π₁ is-rezk-A) x₁ x₁ refl
        , t ≡ 1₂ ↦ iso-eq A (π₁ is-rezk-A) y₁ y₁ refl])
      ( \ t → iso-eq A (π₁ is-rezk-A) (f t) (f t) refl)
      ( g)
      ( map-homotopy-hom2' A (π₁ is-rezk-A) x₁ y₁ f g
        ( triangle-square-left-id-is-segal A (π₁ is-rezk-A)
          ( x₁) (y₁) (y₁)
          ( f) (g) (π₁ (iso-eq A (π₁ is-rezk-A) y₁ y₁ refl)) (σ))))
    ( y₂) (k))
  ( x₂) (h)
  ( g)
  ( σ)
```

```rzk
#def is-iso-arrow-square-sides-iso-is-rezk
  ( A : U)
  ( is-rezk-A : is-rezk A)
  ( x₁ y₁ : A)
  ( x₂ y₂ : A)
  ( f : hom A x₁ y₁)
  ( g : hom A x₂ y₂)
  ( h : Iso A (π₁ is-rezk-A) x₁ x₂)
  ( k : Iso A (π₁ is-rezk-A) y₁ y₂)
  ( σ : curried-square A x₁ y₁ x₂ y₂ f (π₁ h) g (π₁ k))
  : (t : Δ¹) → is-iso-arrow A (π₁ is-rezk-A) (f t) (g t) (\ s → σ t s)
    [ t ≡ 0₂ ↦ π₂ h, t ≡ 1₂ ↦ π₂ k]
  :=
  iso-ind-is-rezk A is-rezk-A x₁
  ( \ x₂ h → (g : hom A x₂ y₂)
    → ( σ : curried-square A x₁ y₁ x₂ y₂ f (π₁ h) g (π₁ k))
    → ( (t : Δ¹) → is-iso-arrow A (π₁ is-rezk-A) (f t) (g t) (\ s → σ t s)
      [ t ≡ 0₂ ↦ π₂ h, t ≡ 1₂ ↦ π₂ k]))
  ( iso-ind-is-rezk A is-rezk-A y₁
    ( \ y₂ k → (g : hom A x₁ y₂)
      → ( σ : curried-square A x₁ y₁ x₁ y₂ f (id-hom A x₁) g (π₁ k))
      → ( (t : Δ¹) → is-iso-arrow A (π₁ is-rezk-A) (f t) (g t) (\ s → σ t s)
        [ t ≡ 0₂ ↦ is-iso-arrow-id-hom A (π₁ is-rezk-A) x₁
        , t ≡ 1₂ ↦ π₂ k]))
    ( \ g σ → ind-curried-square-sides-id-is-segal A (π₁ is-rezk-A) x₁ y₁ f
      ( \ g σ → ( (t : Δ¹) → is-iso-arrow A (π₁ is-rezk-A) (f t) (g t) (\ s → σ t s)
        [ t ≡ 0₂ ↦ is-iso-arrow-id-hom A (π₁ is-rezk-A) x₁
        , t ≡ 1₂ ↦ is-iso-arrow-id-hom A (π₁ is-rezk-A) y₁]))
      ( \ t → is-iso-arrow-id-hom A (π₁ is-rezk-A) (f t))
      ( g)
      ( σ))
    ( y₂) (k))
  ( x₂) (h)
  ( g)
  ( σ)
```

## Dependent Squares

```rzk
#def dsquare
  ( B : U)
  ( x y z w : B)
  ( f₁ : hom B x y)
  ( g₁ : hom B x z)
  ( f₂ : hom B z w)
  ( g₂ : hom B y w)
  ( σ : square B x y z w f₁ g₁ f₂ g₂)
  ( P : B → U)
  ( X : P x)
  ( Y : P y)
  ( Z : P z)
  ( W : P w)
  ( F₁ : dhom B x y f₁ P X Y)
  ( G₁ : dhom B x z g₁ P X Z)
  ( F₂ : dhom B z w f₂ P Z W)
  ( G₂ : dhom B y w g₂ P Y W)
  : U
  :=
  ( (t, s) : 2 × 2) → P (σ (t, s))
  [ t ≡ 0₂ ↦ G₁ s
  , t ≡ 1₂ ↦ G₂ s
  , s ≡ 0₂ ↦ F₁ t
  , s ≡ 1₂ ↦ F₂ t]
```

```rzk
#def equiv-dsquare-glued-dhom2
  ( B : U)
  ( x y z w : B)
  ( f₁ : hom B x y)
  ( g₁ : hom B x z)
  ( f₂ : hom B z w)
  ( g₂ : hom B y w)
  ( σ : square B x y z w f₁ g₁ f₂ g₂)
  ( P : B → U)
  ( X : P x)
  ( Y : P y)
  ( Z : P z)
  ( W : P w)
  ( F₁ : dhom B x y f₁ P X Y)
  ( G₁ : dhom B x z g₁ P X Z)
  ( F₂ : dhom B z w f₂ P Z W)
  ( G₂ : dhom B y w g₂ P Y W)
  : Equiv
    ( dsquare B x y z w f₁ g₁ f₂ g₂ σ P X Y Z W F₁ G₁ F₂ G₂)
    ( Σ (D : dhom B x w (\ t → σ (t, t)) P X W)
      , product
        ( dhom2 B x y w
          ( f₁) (g₂) (\ t → σ (t, t))
          (\ ts → σ ts)
          ( P) (X) (Y) (W)
          ( F₁) (G₂) (D))
        ( dhom2 B x z w
          ( g₁) (f₂) (\ t → σ (t, t))
          (\ (t, s) → σ (s, t))
          ( P) (X) (Z) (W)
          ( G₁) (F₂) (D)))
  :=
  equiv-is-inverse
  ( dsquare B x y z w f₁ g₁ f₂ g₂ σ P X Y Z W F₁ G₁ F₂ G₂)
  ( Σ (D : dhom B x w (\ t → σ (t, t)) P X W)
    , product
      ( dhom2 B x y w
        ( f₁) (g₂) (\ t → σ (t, t))
        (\ ts → σ ts)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( dhom2 B x z w
        ( g₁) (f₂) (\ t → σ (t, t))
        (\ (t, s) → σ (s, t))
        ( P) (X) (Z) (W)
        ( G₁) (F₂) (D)))
  ( \ S → (\ t → S (t, t), (\ ts → S ts, \ (t, s) → S (s, t))))
  ( \ (_, (τ₁, τ₂)) (t, s) → recOR
    ( s ≤ t ↦ τ₁ (t, s)
    , t ≤ s ↦ τ₂ (s, t)))
  ( \ _ → refl)
  ( \ _ → refl)
```

```rzk
#def equiv-dsquare-left-id-dhom2-is-inner-family
  ( B : U)
  ( x y w : B)
  ( f₁ : hom B x y)
  ( f₂ : hom B x w)
  ( g₂ : hom B y w)
  ( τ : hom2 B x y w f₁ g₂ f₂)
  ( P : B → U)
  ( is-inner-family-P : is-inner-family B P)
  ( X : P x)
  ( Y : P y)
  ( W : P w)
  ( F₁ : dhom B x y f₁ P X Y)
  ( F₂ : dhom B x w f₂ P X W)
  ( G₂ : dhom B y w g₂ P Y W)
  : Equiv
    ( dsquare B x y x w f₁ (id-hom B x) f₂ g₂
      ( square-hom2 B x y w f₁ f₂ g₂ τ)
      ( P) X Y X W F₁ (id-dhom B x P X) F₂ G₂)
    ( dhom2 B x y w f₁ g₂ f₂ τ P X Y W F₁ G₂ F₂)
  :=
  equiv-quadruple-comp
  ( dsquare B x y x w f₁ (id-hom B x) f₂ g₂
    ( square-hom2 B x y w f₁ f₂ g₂ τ)
    ( P) X Y X W F₁ (id-dhom B x P X) F₂ G₂)
  ( Σ (D : dhom B x w f₂ P X W)
    , product
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( dhom2 B x x w
        ( id-hom B x) (f₂) (f₂)
        ( \ (_, s) → f₂ s)
        ( P) (X) (X) (W)
        ( id-dhom B x P X) (F₂) (D)))
  ( Σ (D : dhom B x w f₂ P X W)
    , product
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( F₂ = D))
  ( Σ (D : dhom B x w f₂ P X W)
    , product
      ( F₂ = D)
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D)))
  ( dhom2 B x y w f₁ g₂ f₂ τ P X Y W F₁ G₂ F₂)
  ( equiv-dsquare-glued-dhom2 B x y x w f₁ (id-hom B x) f₂ g₂
    ( square-hom2 B x y w f₁ f₂ g₂ τ) P X Y X W F₁ (id-dhom B x P X) F₂ G₂)
  ( total-equiv-family-of-equiv
    ( dhom B x w f₂ P X W)
    ( \ D → product
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( dhom2 B x x w
        ( id-hom B x) (f₂) (f₂)
        ( \ (_, s) → f₂ s)
        ( P) (X) (X) (W)
        ( id-dhom B x P X) (F₂) (D)))
    ( \ D → product
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( F₂ = D))
    ( \ D → equiv-product-equivs
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( equiv-identity
        ( dhom2 B x y w
          ( f₁) (g₂) (f₂)
          ( τ)
          ( P) (X) (Y) (W)
          ( F₁) (G₂) (D)))
      ( dhom2 B x x w
        ( id-hom B x) (f₂) (f₂)
        ( \ (_, s) → f₂ s)
        ( P) (X) (X) (W)
        ( id-dhom B x P X) (F₂) (D))
      ( F₂ = D)
      ( inv-equiv
        ( F₂ = D)
        ( dhom2 B x x w
          ( id-hom B x) (f₂) (f₂)
          ( \ (_, s) → f₂ s)
          ( P) (X) (X) (W)
          ( id-dhom B x P X) (F₂) (D))
        ( equiv-homotopy-dhom2-is-inner-family B x w f₂
          ( P) is-inner-family-P X W F₂ D))))
  ( equiv-is-inverse
    ( Σ (D : dhom B x w f₂ P X W)
      , product
        ( dhom2 B x y w
          ( f₁) (g₂) (f₂)
          ( τ)
          ( P) (X) (Y) (W)
          ( F₁) (G₂) (D))
        ( F₂ = D))
    ( Σ (D : dhom B x w f₂ P X W)
      , product
        ( F₂ = D)
        ( dhom2 B x y w
          ( f₁) (g₂) (f₂)
          ( τ)
          ( P) (X) (Y) (W)
          ( F₁) (G₂) (D)))
    ( \ (D, (τ', p)) → (D, (p, τ')))
    ( \ (D, (p, τ')) → (D, (τ', p)))
    ( \ _ → refl)
    ( \ _ → refl))
  ( equiv-based-paths-family (dhom B x w f₂ P X W)
    ( \ D → dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
    ( F₂))
```
