# Squares and Triangles

```rzk
#lang rzk-1
```

```rzk
--#assume TODO : (A : U) → A
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
#def σ-eq-iso-square-sides-iso-is-rezk
  ( A : U)
  ( is-rezk-A : is-rezk A)
  ( x₁ y₁ : A)
  ( x₂ y₂ : A)
  ( f : hom A x₁ y₁)
  ( g : hom A x₂ y₂)
  ( h : Iso A (π₁ is-rezk-A) x₁ x₂)
  ( k : Iso A (π₁ is-rezk-A) y₁ y₂)
  ( σ : square A x₁ y₁ x₂ y₂ f (π₁ h) g (π₁ k))
  : ( \ t → iso-square-sides-iso-is-rezk A is-rezk-A
      ( x₁) (y₁) ( x₂) (y₂)
      ( f) (g) (h) (k) (σ)
      ( t))
    = (\ t s → σ (t, s))
```

```rzkk
#def is-iso-arrow-nat-trans-is-iso-arrow-boundary
  ( A : U)
  ( is-rezk-A : is-rezk A)
  ( x₁ y₁ : A)
  ( x₂ y₂ : A)
  ( f : hom A x₁ y₁)
  ( g : hom A x₂ y₂)
  ( α : (t : Δ¹) → hom A (f t) (g t))
  ( is-iso-α-0 : is-iso-arrow A (π₁ is-rezk-A) x₁ x₂ (α 0₂))
  ( is-iso-α-1 : is-iso-arrow A (π₁ is-rezk-A) y₁ y₂ (α 1₂))
  : ( t : Δ¹) → is-iso-arrow A (π₁ is-rezk-A) (f t) (g t) (α t)
    [t ≡ 0₂ ↦ is-iso-α-0, t ≡ 1₂ ↦ is-iso-α-1]
  :=
  \ t → π₂ (iso-square-sides-iso-is-rezk A is-rezk-A x₁ y₁ x₂ y₂
  ( f)
  ( g)
  ( α 0₂, is-iso-α-0)
  ( α 1₂, is-iso-α-1)
  ( \ (t, s) → α t s)
  ( t))
```

```rzkk

#def equiv
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( f g : (t : Δ¹) → A [t ≡ 0₂ ↦ a])

```

```rzkk


#def t
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( f g : (t : Δ¹) → A [t ≡ 0₂ ↦ a])
  : Equiv
    ( ((t₁, t₂) : 2 × 2) → A [t₂ ≡ 0₂ ↦ f t₁, t₂ ≡ 1₂ ↦ g t₁, t₁ ≡ 0₂ ↦ a])
    ( ((t₁, t₂) : Δ²) → A [t₂ ≡ 0₂ ↦ f t₁, t₁ ≡ t₂ ↦ g t₁])
  :=
  equiv-comp
  ( ((t₁, t₂) : 2 × 2) → A [t₂ ≡ 0₂ ↦ f t₁, t₂ ≡ 1₂ ↦ g t₁, t₁ ≡ 0₂ ↦ a])
  ( Σ (f' : (t : Δ¹) → A [t ≡ 0₂ ↦ a])
    , product
      ( f = f')
      ( ((t₁, t₂) : Δ²) → A [t₂ ≡ 0₂ ↦ f' t₁, t₁ ≡ t₂ ↦ g t₁]))
  ( ((t₁, t₂) : Δ²) → A [t₂ ≡ 0₂ ↦ f t₁, t₁ ≡ t₂ ↦ g t₁])
  ( equiv-is-inverse
    ( ((t₁, t₂) : 2 × 2) → A [t₂ ≡ 0₂ ↦ f t₁, t₂ ≡ 1₂ ↦ g t₁, t₁ ≡ 0₂ ↦ a])
    ( Σ (g' : (t : Δ¹) → A [t ≡ 0₂ ↦ a, t ≡ 1₂ ↦ g 1₂])
      , product
        ( g = g')
        ( ((t₁, t₂) : Δ²) → A [t₂ ≡ 0₂ ↦ f t₁, t₁ ≡ t₂ ↦ g' t₁]))
    ( \ σ → ( \ t → σ (t, t)
      , ( map-homotopy-hom2 A is-segal-A
          ( a) ( g 1₂)
          ( \ t → g t) ( \ t → σ (t, t))
          ( \ (t₁, t₂) → σ (t₂, t₁))
        , \ tt → σ tt)))
    ( \ (g', (p, σ)) (t₁, t₂) → recOR
      ( t₂ ≤ t₁ ↦ σ (t₁, t₂)
      , t₁ ≤ t₂ ↦ map-hom2-homotopy A a (g 1₂) (\ t → g t) g' p (t₂, t₁)))
    ( \ _ → refl)
    ( \ _ → refl))
  ( equiv-based-paths-family
    ( (t : Δ¹) → A [t ≡ 0₂ ↦ a])
    ( \ f' → ( ((t₁, t₂) : Δ²) → A [t₂ ≡ 0₂ ↦ f' t₁, t₁ ≡ t₂ ↦ g t₁]))
    ( f))


```
