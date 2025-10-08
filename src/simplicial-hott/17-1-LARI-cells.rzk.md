# Pullbacks of LARI families

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#section LARI-cells

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variable B : U
#variable P : B → U
```

```rzk
#def is-LARI-cell
  ( v : ψ → B)
  ( g : (t : ψ) → P (v t))
  : U
  :=
    ( w : ψ → B)
  → ( m : (t : ψ) → P (w t))
  → ( α₂ : ((t, s) : 2 × I | Δ¹ t ∧ ψ s) → B [t ≡ 0₂ ↦ v s, t ≡ 1₂ ↦ w s])
  → ( α₃ : ((t, s) : 2 × I | Δ¹ t ∧ ϕ s) → P (α₂ (t, s))
      [ t ≡ 0₂ ↦ g s, t ≡ 1₂ ↦ m s])
  → is-contr (
    ( (t, s) : 2 × I | Δ¹ t ∧ ψ s) → P (α₂ (t, s))
    [ t ≡ 0₂ ↦ g s, t ≡ 1₂ ↦ m s, ϕ s ↦ α₃ (t, s)])
```

```rzk
#def has-enough-LARI-lifts
  : U
  :=
    ( v : ψ → B)
  → ( f : (t : ϕ) → P (v t))
  → ( Σ ( g : (t : ψ) → P (v t) [ϕ t ↦ f t]) , is-LARI-cell v g)
```

```rzk
#def is-LARI-family-has-enough-LARI-lifts
  ( has-enough-LARI-lifts-P : has-enough-LARI-lifts)
  : is-LARI-family I ψ ϕ B P
  :=
  \ g f₀ → (π₁ (has-enough-LARI-lifts-P g f₀)
  , \ f → is-contr-equiv-is-contr
    ( ((t, s) : 2 × I | Δ¹ t ∧ ψ s) → P (g s)
      [ t ≡ 0₂ ↦ π₁ (has-enough-LARI-lifts-P g f₀) s
      , t ≡ 1₂ ↦ f s
      , ϕ s ↦ f₀ s])
    ( hom ((t : ψ) → P (g t) [ϕ t ↦ f₀ t])
      ( π₁ (has-enough-LARI-lifts-P g f₀))
      ( f))
    ( equiv-is-inverse
      ( ((t, s) : 2 × I | Δ¹ t ∧ ψ s) → P (g s)
        [ t ≡ 0₂ ↦ π₁ (has-enough-LARI-lifts-P g f₀) s
        , t ≡ 1₂ ↦ f s
        , ϕ s ↦ f₀ s])
      ( hom ((s : ψ) → P (g s) [ϕ s ↦ f₀ s])
        ( π₁ (has-enough-LARI-lifts-P g f₀))
        ( f))
      ( \ σ t s → σ (t, s))
      ( \ γ (t, s) → γ t s)
      ( \ _ → refl)
      ( \ _ → refl))
    ( π₂ (has-enough-LARI-lifts-P g f₀) g f
      ( \ (_, s) → g s)
      ( \ (_, s) → f₀ s)))
```

```rzk
#def has-enough-LARI-lifts-is-LARI-family-is-inner-type-fam
  ( is-LARI-family-P : is-LARI-family I ψ ϕ B P)
  ( is-inner-fib-type-fam-P
    : is-inner-fib-type-fam
      ( Σ (vw : ψ → B), (s : ϕ) → P (vw s))
      ( \ (vw, f₀) → ((s : ψ) → P (vw s) [ϕ s ↦ f₀ s])))
  : has-enough-LARI-lifts
  :=
  \ v f → (π₁ (is-LARI-family-P v f)
  , \ w m α₂ α₃ → is-contr-equiv-is-contr
    ( dhom (Σ (vw : ψ → B) , (s : ϕ) → P (vw s))
      ( v, f) ( w, \ s → m s)
      ( \ t → (\ s → α₂ (t, s), \ s → α₃ (t, s)))
      ( \ (vw, f₀) → ((s : ψ) → P (vw s) [ϕ s ↦ f₀ s]))
      ( π₁ (is-LARI-family-P v f))
      ( m))
    ( ((t, s) : 2 × I | Δ¹ t ∧ ψ s) → P (α₂ (t, s))
      [ t ≡ 0₂ ↦ π₁ (is-LARI-family-P v f) s
      , t ≡ 1₂ ↦ m s
      , ϕ s ↦ α₃ (t, s)])
    ( equiv-is-inverse
      ( dhom (Σ (vw : ψ → B) , (s : ϕ) → P (vw s))
        ( v, f) ( w, \ s → m s)
        ( \ t → (\ s → α₂ (t, s), \ s → α₃ (t, s)))
        ( \ (vw, f₀) → ((s : ψ) → P (vw s) [ϕ s ↦ f₀ s]))
        ( π₁ (is-LARI-family-P v f))
        ( m))
      ( ((t, s) : 2 × I | Δ¹ t ∧ ψ s) → P (α₂ (t, s))
        [ t ≡ 0₂ ↦ π₁ (is-LARI-family-P v f) s
        , t ≡ 1₂ ↦ m s
        , ϕ s ↦ α₃ (t, s)])
      ( \ γ (t, s) → γ t s)
      ( \ σ t s → σ (t, s))
      ( \ _ → refl)
      ( \ _ → refl))
    ( is-dhom-initial-has-initial-is-inner-fib-type-fam
      ( Σ (vw : ψ → B) , (s : ϕ) → P (vw s))
      ( \ (vw, f₀) → ((s : ψ) → P (vw s) [ϕ s ↦ f₀ s]))
      ( \ (vw, f₀) → is-LARI-family-P vw f₀)
      ( is-inner-fib-type-fam-P)
      ( v, f)
      ( w, \ s → m s)
      ( m)
      ( \ t → (\ s → α₂ (t, s), \ s → α₃ (t, s)))))
```

```rzk
#end LARI-cells
```

```rzk
#def is-cocartesian-family-has-enough-LARI-lifts
  ( B : U)
  ( P : B → U)
  ( is-isoinner-family-P : is-isoinner-family B P)
  ( has-enough-LARI-lifts-P : has-enough-LARI-lifts 2 Δ¹ (\ t → t ≡ 0₂) B P)
  : is-cocartesian-family B P
  :=
  ( is-isoinner-family-P
  , \ b b' u e →
    ( π₁ (has-enough-LARI-lifts u (\ _ → e)) 1₂
    , ( π₁ (has-enough-LARI-lifts u (\ _ → e))
      , \ b'' v w σ e'' h → is-contr-equiv-is-contr
        ( ( (t, s) : 2 × 2 | Δ¹ t ∧ Δ¹ s)
          → P (recOR(s ≤ t ↦ σ (t, s), t ≤ s ↦ b))
          [ t ≡ 0₂ ↦ π₁ (has-enough-LARI-lifts u (\ _ → e)) s
          , t ≡ 1₂ ↦ h s
          , s ≡ 0₂ ↦ e])
        ( Σ ( g : dhom B b' b'' v P e' e'')
        , ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h))
        ( equiv-is-inverse
          ( ( (t, s) : 2 × 2 | Δ¹ t ∧ Δ¹ s)
            → P (recOR(s ≤ t ↦ σ (t, s), t ≤ s ↦ b))
            [ t ≡ 0₂ ↦ π₁ (has-enough-LARI-lifts u (\ _ → e)) s
            , t ≡ 1₂ ↦ h s
            , s ≡ 0₂ ↦ e])
          ( Σ ( g : dhom B b' b'' v P e' e'')
          , ( dhom2 B b b' b'' u v w σ P e e' e'' f g h))
          ( \ σ → ((\ t → σ (1₂, t))
            , π₁ ()))
        )
        ( π₂ (has-enough-LARI-lifts u (\ _ → e))
          ( w) (\ _ → e) (\ (t, s) → recOR(s ≤ t ↦ σ (t, s), t ≤ s ↦ b))
          ( \ _ → e))
      )))
```
