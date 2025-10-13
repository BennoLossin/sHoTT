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
  → is-contr
    ( ( (t, s) : 2 × I | Δ¹ t ∧ ψ s) → P (α₂ (t, s))
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
  ( is-inner-family-P
    : is-inner-family
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
    ( is-dhom-initial-has-initial-is-inner-family
      ( Σ (vw : ψ → B) , (s : ϕ) → P (vw s))
      ( \ (vw, f₀) → ((s : ψ) → P (vw s) [ϕ s ↦ f₀ s]))
      ( \ (vw, f₀) → is-LARI-family-P vw f₀)
      ( is-inner-family-P)
      ( v, f)
      ( w, \ s → m s)
      ( m)
      ( \ t → (\ s → α₂ (t, s), \ s → α₃ (t, s)))))
```

```rzk
#end LARI-cells
```

```rzk
#section is-cocartesian-family-has-enough-LARI-lifts

#variable B : U
#variable P : B → U
#variable is-isoinner-family-P : is-isoinner-family B P
#variable has-enough-LARI-lifts-P : has-enough-LARI-lifts 2 Δ¹ (\ t → t ≡ 0₂) B P

#def toname-equiv-3
  ( b b' b'' : B)
  ( u : hom B b b')
  ( v : hom B b' b'')
  ( w : hom B b b'')
  ( τ : hom2 B b b' b'' u v w)
  ( e : P b)
  ( e'' : P b'')
  ( h : dhom B b b'' w P e e'')
  : Equiv
    ( ( (t, s) : 2 × 2 | Δ¹ t ∧ Δ¹ s)
      → P (recOR(t ≤ s ↦ τ (s, t), s ≤ t ↦ w s))
      [ t ≡ 0₂ ↦ π₁ (has-enough-LARI-lifts-P u (\ _ → e)) s
      , t ≡ 1₂ ↦ h s
      , s ≡ 0₂ ↦ e])
    ( Σ ( gg : dhom B b' b'' v P
             ( π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂)
             ( e''))
      , dsquare B b b' b b'' u (id-hom B b) w v
        ( square-hom2 B b b' b'' u w v τ)
        ( P) e (π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂) e e''
        ( \ t → π₁ (has-enough-LARI-lifts-P u (\ _ → e)) t) (id-dhom B b P e) h gg)
  :=
  equiv-is-inverse
  ( ( (t, s) : 2 × 2 | Δ¹ t ∧ Δ¹ s)
    → P (recOR(t ≤ s ↦ τ (s, t), s ≤ t ↦ w s))
    [ t ≡ 0₂ ↦ π₁ (has-enough-LARI-lifts-P u (\ _ → e)) s
    , t ≡ 1₂ ↦ h s
    , s ≡ 0₂ ↦ e])
  ( Σ ( gg : dhom B b' b'' v P
             ( π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂)
             ( e''))
    , dsquare B b b' b b'' u (id-hom B b) w v
      ( square-hom2 B b b' b'' u w v τ)
      ( P) e (π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂) e e''
      ( \ t → π₁ (has-enough-LARI-lifts-P u (\ _ → e)) t) (id-dhom B b P e) h gg)
  ( \ σ → (\ t → σ (t, 1₂), \ (t, s) → σ (s, t)))
  ( \ (_, σ) (t, s) → σ (s, t))
  ( \ _ → refl)
  ( \ _ → refl)

#def toname-equiv
  ( b b' b'' : B)
  ( u : hom B b b')
  ( v : hom B b' b'')
  ( w : hom B b b'')
  ( τ : hom2 B b b' b'' u v w)
  ( e : P b)
  ( e'' : P b'')
  ( h : dhom B b b'' w P e e'')
  : Equiv
    ( ( (t, s) : 2 × 2 | Δ¹ t ∧ Δ¹ s)
      → P (recOR(t ≤ s ↦ τ (s, t), s ≤ t ↦ w s))
      [ t ≡ 0₂ ↦ π₁ (has-enough-LARI-lifts-P u (\ _ → e)) s
      , t ≡ 1₂ ↦ h s
      , s ≡ 0₂ ↦ e])
    ( Σ ( gg : dhom B b' b'' v P
               ( π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂)
               ( e''))
      , ( dhom2 B b b' b'' u v w τ P
          ( e) (π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂) e''
          ( \ t → π₁ (has-enough-LARI-lifts-P u (\ _ → e)) t) gg h))
  :=
  equiv-comp
  ( ( (t, s) : 2 × 2 | Δ¹ t ∧ Δ¹ s)
    → P (recOR(t ≤ s ↦ τ (s, t), s ≤ t ↦ w s))
    [ t ≡ 0₂ ↦ π₁ (has-enough-LARI-lifts-P u (\ _ → e)) s
    , t ≡ 1₂ ↦ h s
    , s ≡ 0₂ ↦ e])
  ( Σ ( gg : dhom B b' b'' v P
             ( π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂)
             ( e''))
    , dsquare B b b' b b'' u (id-hom B b) w v
      ( square-hom2 B b b' b'' u w v τ)
      ( P) e (π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂) e e''
      ( \ t → π₁ (has-enough-LARI-lifts-P u (\ _ → e)) t) (id-dhom B b P e) h gg)
  ( Σ ( gg : dhom B b' b'' v P
             ( π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂)
             ( e''))
    , dhom2 B b b' b'' u v w τ P
      ( e) (π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂) e''
      ( \ t → π₁ (has-enough-LARI-lifts-P u (\ _ → e)) t) gg h)
  ( toname-equiv-3 b b' b'' u v w τ e e'' h)
  ( total-equiv-family-of-equiv
    ( dhom B b' b'' v P
      ( π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂)
      ( e''))
    ( \ gg → dsquare B b b' b b'' u (id-hom B b) w v
      ( square-hom2 B b b' b'' u w v τ)
      ( P) e (π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂) e e''
      ( \ t → π₁ (has-enough-LARI-lifts-P u (\ _ → e)) t) (id-dhom B b P e) h gg)
    ( \ gg → dhom2 B b b' b'' u v w τ P
      ( e) (π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂) e''
      ( \ t → π₁ (has-enough-LARI-lifts-P u (\ _ → e)) t) gg h)
    ( \ gg → equiv-dsquare-left-id-dhom2-is-inner-family
      ( B) b b' b'' u w v τ
      ( P) (π₁ is-isoinner-family-P) e
      ( π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂) e''
      ( \ t → π₁ (has-enough-LARI-lifts-P u (\ _ → e)) t) h gg))

#def is-cocartesian-family-has-enough-LARI-lifts-is-isoinner-family
  : is-cocartesian-family B P
  :=
  ( is-isoinner-family-P
  , \ b b' u e →
    ( π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂
    , ( \ t → π₁ (has-enough-LARI-lifts-P u (\ _ → e)) t
      , \ b'' v w σ e'' h → is-contr-equiv-is-contr
        ( ( (t, s) : 2 × 2 | Δ¹ t ∧ Δ¹ s)
          → P (recOR(t ≤ s ↦ σ (s, t), s ≤ t ↦ w s))
          [ t ≡ 0₂ ↦ π₁ (has-enough-LARI-lifts-P u (\ _ → e)) s
          , t ≡ 1₂ ↦ h s
          , s ≡ 0₂ ↦ e])
        ( Σ ( gg : dhom B b' b'' v P
                   ( π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂)
                   ( e''))
          , ( dhom2 B b b' b'' u v w σ P
              ( e) (π₁ (has-enough-LARI-lifts-P u (\ _ → e)) 1₂) e''
              ( \ t → π₁ (has-enough-LARI-lifts-P u (\ _ → e)) t) gg h))
        ( toname-equiv b b' b'' u v w σ e e'' h)
        ( π₂ (has-enough-LARI-lifts-P u (\ _ → e))
          ( w) h
          ( \ (t, s) → recOR(t ≤ s ↦ σ (s, t), s ≤ t ↦ w s))
          ( \ _ → e)))))

#end is-cocartesian-family-has-enough-LARI-lifts
```

```rzk
#def toname-equiv-4
  ( B : U)
  ( P : B → U)
  ( v : Δ¹ → B)
  ( f : (s : 2 | s ≡ 0₂) → P (v s))
  ( g : (s : Δ¹) → P (v s) [s ≡ 0₂ ↦ f 0₂])
  ( w : Δ¹ → B)
  ( m : (s : Δ¹) → P (w s))
  ( α₂ : ((t, s) : 2 × 2 | Δ¹ t ∧ Δ¹ s) → B [t ≡ 0₂ ↦ v s, t ≡ 1₂ ↦ w s])
  ( α₃ : ((t, s) : 2 × 2 | Δ¹ t ∧ s ≡ 0₂) → P (α₂ (t, s))
         [t ≡ 0₂ ↦ g s, t ≡ 1₂ ↦ m s])
  : Equiv
    ( ( (t, s) : 2 × 2 | Δ¹ t ∧ Δ¹ s) → P (α₂ (t, s))
      [ t ≡ 0₂ ↦ g s, t ≡ 1₂ ↦ m s, s ≡ 0₂ ↦ α₃ (t, s)])
    ( Σ (D : dhom B (v 0₂) (w 1₂) (\ t → α₂ (t, t)) P (f 0₂) (m 1₂))
      , product
        ( Σ (h : (t : Δ¹) → P (α₂ (t, 1₂)) [t ≡ 0₂ ↦ g 1₂, t ≡ 1₂ ↦ m 1₂])
          , dhom2 B (v 0₂) (v 1₂) (w 1₂)
            ( v) (\ t → α₂ (t, 1₂)) (\ s → α₂ (s, s))
            ( \ (t, s) → α₂ (s, t))
            ( P) (f 0₂) (g 1₂) (m 1₂)
            ( \ s → g s) (h) (D))
        ( dhom2 B (v 0₂) (w 0₂) (w 1₂)
          ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
          ( \ ts → α₂ ts)
          ( P) (f 0₂) (m 0₂) (m 1₂)
          ( \ t → α₃ (t, 0₂)) (m) (D)))
  :=
  equiv-triple-comp
  ( ( (t, s) : 2 × 2 | Δ¹ t ∧ Δ¹ s) → P (α₂ (t, s))
      [ t ≡ 0₂ ↦ g s, t ≡ 1₂ ↦ m s, s ≡ 0₂ ↦ α₃ (t, s)])
  ( Σ (h : (t : Δ¹) → P (α₂ (t, 1₂)) [t ≡ 0₂ ↦ g 1₂, t ≡ 1₂ ↦ m 1₂])
    , dsquare B (v 0₂) (v 1₂) (w 0₂) (w 1₂)
      ( v) (\ t → α₂ (t, 0₂)) (w) (\ t → α₂ (t, 1₂))
      ( \ (t, s) → α₂ (s, t)) (P)
      ( f 0₂) (g 1₂) (m 0₂) (m 1₂)
      ( \ s → g s) (\ t → α₃ (t, 0₂)) (m) (h))
  ( Σ (h : (t : Δ¹) → P (α₂ (t, 1₂)) [t ≡ 0₂ ↦ g 1₂, t ≡ 1₂ ↦ m 1₂])
    , ( Σ (D : dhom B (v 0₂) (w 1₂) (\ s → α₂ (s, s)) P (f 0₂) (m 1₂))
      , product
        ( dhom2 B (v 0₂) (v 1₂) (w 1₂)
          ( v) (\ t → α₂ (t, 1₂)) (\ t → α₂ (t, t))
          ( \ (t, s) → α₂ (s, t))
          ( P) (f 0₂) (g 1₂) (m 1₂)
          ( \ s → g s) (h) (D))
        ( dhom2 B (v 0₂) (w 0₂) (w 1₂)
          ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
          ( \ ts → α₂ ts)
          ( P) (f 0₂) (m 0₂) (m 1₂)
          ( \ t → α₃ (t, 0₂)) (m) (D))))
  ( Σ (D : dhom B (v 0₂) (w 1₂) (\ t → α₂ (t, t)) P (f 0₂) (m 1₂))
    , product
      ( Σ (h : (t : Δ¹) → P (α₂ (t, 1₂)) [t ≡ 0₂ ↦ g 1₂, t ≡ 1₂ ↦ m 1₂])
        , dhom2 B (v 0₂) (v 1₂) (w 1₂)
          ( v) (\ t → α₂ (t, 1₂)) (\ s → α₂ (s, s))
          ( \ (t, s) → α₂ (s, t))
          ( P) (f 0₂) (g 1₂) (m 1₂)
          ( \ s → g s) (h) (D))
      ( dhom2 B (v 0₂) (w 0₂) (w 1₂)
        ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
        ( \ ts → α₂ ts)
        ( P) (f 0₂) (m 0₂) (m 1₂)
        ( \ t → α₃ (t, 0₂)) (m) (D)))
  ( equiv-is-inverse
    ( ( (t, s) : 2 × 2 | Δ¹ t ∧ Δ¹ s) → P (α₂ (t, s))
      [ t ≡ 0₂ ↦ g s, t ≡ 1₂ ↦ m s, s ≡ 0₂ ↦ α₃ (t, s)])
    ( Σ (h : (t : Δ¹) → P (α₂ (t, 1₂)) [t ≡ 0₂ ↦ g 1₂, t ≡ 1₂ ↦ m 1₂])
      , dsquare B (v 0₂) (v 1₂) (w 0₂) (w 1₂)
        ( v) (\ t → α₂ (t, 0₂)) (w) (\ t → α₂ (t, 1₂))
        ( \ (t, s) → α₂ (s, t)) (P)
        ( f 0₂) (g 1₂) (m 0₂) (m 1₂)
        ( \ s → g s) (\ t → α₃ (t, 0₂)) (m) (h))
    ( \ σ → (\ t → σ (t, 1₂), \ (t, s) → σ (s, t)))
    ( \ (_, σ) (t, s) → σ (s, t))
    ( \ _ → refl)
    ( \ _ → refl))
  ( total-equiv-family-of-equiv
    ( (t : Δ¹) → P (α₂ (t, 1₂)) [t ≡ 0₂ ↦ g 1₂, t ≡ 1₂ ↦ m 1₂])
    ( \ h → dsquare B (v 0₂) (v 1₂) (w 0₂) (w 1₂)
      ( v) (\ t → α₂ (t, 0₂)) (w) (\ t → α₂ (t, 1₂))
      ( \ (t, s) → α₂ (s, t)) (P)
      ( f 0₂) (g 1₂) (m 0₂) (m 1₂)
      ( \ s → g s) (\ t → α₃ (t, 0₂)) (m) (h))
    ( \ h → Σ (D : dhom B (v 0₂) (w 1₂) (\ t → α₂ (t, t)) P (f 0₂) (m 1₂))
      , product
        ( dhom2 B (v 0₂) (v 1₂) (w 1₂)
          ( v) (\ t → α₂ (t, 1₂)) (\ s → α₂ (s, s))
          ( \ (t, s) → α₂ (s, t))
          ( P) (f 0₂) (g 1₂) (m 1₂)
          ( \ s → g s) (h) (D))
        ( dhom2 B (v 0₂) (w 0₂) (w 1₂)
          ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
          ( \ ts → α₂ ts)
          ( P) (f 0₂) (m 0₂) (m 1₂)
          ( \ t → α₃ (t, 0₂)) (m) (D)))
    ( equiv-dsquare-glued-dhom2 B (v 0₂) (v 1₂) (w 0₂) (w 1₂)
      ( v) (\ t → α₂ (t, 0₂)) (w) (\ t → α₂ (t, 1₂)) (\ (t, s) → α₂ (s, t))
      ( P) (f 0₂) (g 1₂) (m 0₂) (m 1₂) (\ s → g s) (\ t → α₃ (t, 0₂)) (m)))
  ( equiv-is-inverse
    ( Σ (h : (t : Δ¹) → P (α₂ (t, 1₂)) [t ≡ 0₂ ↦ g 1₂, t ≡ 1₂ ↦ m 1₂])
      , ( Σ (D : dhom B (v 0₂) (w 1₂) (\ t → α₂ (t, t)) P (f 0₂) (m 1₂))
        , product
          ( dhom2 B (v 0₂) (v 1₂) (w 1₂)
            ( v) (\ t → α₂ (t, 1₂)) (\ s → α₂ (s, s))
            ( \ (t, s) → α₂ (s, t))
            ( P) (f 0₂) (g 1₂) (m 1₂)
            ( \ s → g s) (h) (D))
          ( dhom2 B (v 0₂) (w 0₂) (w 1₂)
            ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
            ( \ ts → α₂ ts)
            ( P) (f 0₂) (m 0₂) (m 1₂)
            ( \ t → α₃ (t, 0₂)) (m) (D))))
    ( Σ (D : dhom B (v 0₂) (w 1₂) (\ t → α₂ (t, t)) P (f 0₂) (m 1₂))
      , product
        ( Σ (h : (t : Δ¹) → P (α₂ (t, 1₂)) [t ≡ 0₂ ↦ g 1₂, t ≡ 1₂ ↦ m 1₂])
          , dhom2 B (v 0₂) (v 1₂) (w 1₂)
            ( v) (\ t → α₂ (t, 1₂)) (\ s → α₂ (s, s))
            ( \ (t, s) → α₂ (s, t))
            ( P) (f 0₂) (g 1₂) (m 1₂)
            ( \ s → g s) (h) (D))
        ( dhom2 B (v 0₂) (w 0₂) (w 1₂)
          ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
          ( \ ts → α₂ ts)
          ( P) (f 0₂) (m 0₂) (m 1₂)
          ( \ t → α₃ (t, 0₂)) (m) (D)))
    ( \ (h, (D, (τ₁, τ₂))) → (D, ((h, τ₁), τ₂)))
    ( \ (D, ((h, τ₁), τ₂)) → (h, (D, (τ₁, τ₂))))
    ( \ _ → refl)
    ( \ _ → refl))

#def toname-contr
  ( B : U)
  ( P : B → U)
  ( is-inner-family-P : is-inner-family B P)
  ( is-cocartesian-family-P : is-cocartesian-family B P)
  ( v : Δ¹ → B)
  ( f : (s : 2 | s ≡ 0₂) → P (v s))
  ( w : Δ¹ → B)
  ( m : (s : Δ¹) → P (w s))
  ( α₂ : ((t, s) : 2 × 2 | Δ¹ t ∧ Δ¹ s) → B [t ≡ 0₂ ↦ v s, t ≡ 1₂ ↦ w s])
  ( α₃ : ((t, s) : 2 × 2 | Δ¹ t ∧ s ≡ 0₂) → P (α₂ (t, s))
         [t ≡ 0₂ ↦ (π₁ (π₂ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂)))) s, t ≡ 1₂ ↦ m s])
  : is-contr
    ( Σ (D : dhom B (v 0₂) (w 1₂) (\ t → α₂ (t, t)) P (f 0₂) (m 1₂))
      , product
        ( Σ (h : (t : Δ¹) → P (α₂ (t, 1₂))
                 [ t ≡ 0₂ ↦
                   ( π₁ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂)))
                 , t ≡ 1₂ ↦ m 1₂])
          , dhom2 B (v 0₂) (v 1₂) (w 1₂)
            ( v) (\ t → α₂ (t, 1₂)) (\ s → α₂ (s, s))
            ( \ (t, s) → α₂ (s, t))
            ( P) (f 0₂) (π₁ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂))) (m 1₂)
            ( \ s → (π₁ (π₂ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂)))) s) (h) (D))
        ( dhom2 B (v 0₂) (w 0₂) (w 1₂)
          ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
          ( \ ts → α₂ ts)
          ( P) (f 0₂) (m 0₂) (m 1₂)
          ( \ t → α₃ (t, 0₂)) (m) (D)))
  :=
  is-contr-equiv-is-contr'
  ( Σ (D : dhom B (v 0₂) (w 1₂) (\ t → α₂ (t, t)) P (f 0₂) (m 1₂))
    , product
      ( Σ (h : (t : Δ¹) → P (α₂ (t, 1₂))
               [ t ≡ 0₂ ↦
                ( π₁ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂)))
               , t ≡ 1₂ ↦ m 1₂])
        , dhom2 B (v 0₂) (v 1₂) (w 1₂)
          ( v) (\ t → α₂ (t, 1₂)) (\ s → α₂ (s, s))
          ( \ (t, s) → α₂ (s, t))
          ( P) (f 0₂) (π₁ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂))) (m 1₂)
          ( \ s → (π₁ (π₂ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂)))) s) (h) (D))
      ( dhom2 B (v 0₂) (w 0₂) (w 1₂)
        ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
        ( \ ts → α₂ ts)
        ( P) (f 0₂) (m 0₂) (m 1₂)
        ( \ t → α₃ (t, 0₂)) (m) (D)))
  ( ((t, s) : Δ²) → P (α₂ (t, s)) [s ≡ 0₂ ↦ α₃ (t, 0₂), t ≡ 1₂ ↦ m s])
  ( equiv-comp
    ( Σ (D : dhom B (v 0₂) (w 1₂) (\ t → α₂ (t, t)) P (f 0₂) (m 1₂))
      , product
        ( Σ (h : (t : Δ¹) → P (α₂ (t, 1₂))
                 [ t ≡ 0₂ ↦
                   ( π₁ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂)))
                 , t ≡ 1₂ ↦ m 1₂])
          , dhom2 B (v 0₂) (v 1₂) (w 1₂)
            ( v) (\ t → α₂ (t, 1₂)) (\ s → α₂ (s, s))
            ( \ (t, s) → α₂ (s, t))
            ( P) (f 0₂) (π₁ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂))) (m 1₂)
            ( \ s → (π₁ (π₂ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂)))) s) (h) (D))
        ( dhom2 B (v 0₂) (w 0₂) (w 1₂)
          ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
          ( \ ts → α₂ ts)
          ( P) (f 0₂) (m 0₂) (m 1₂)
          ( \ t → α₃ (t, 0₂)) (m) (D)))
    ( Σ (D : dhom B (v 0₂) (w 1₂) (\ t → α₂ (t, t)) P (f 0₂) (m 1₂))
      , dhom2 B (v 0₂) (w 0₂) (w 1₂)
        ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
        ( \ ts → α₂ ts)
        ( P) (f 0₂) (m 0₂) (m 1₂)
        ( \ t → α₃ (t, 0₂)) (m) (D))
    ( ((t, s) : Δ²) → P (α₂ (t, s)) [s ≡ 0₂ ↦ α₃ (t, 0₂), t ≡ 1₂ ↦ m s])
    ( total-equiv-family-of-equiv
      ( dhom B (v 0₂) (w 1₂) (\ t → α₂ (t, t)) P (f 0₂) (m 1₂))
      ( \ D → product
        ( Σ (h : (t : Δ¹) → P (α₂ (t, 1₂))
                 [ t ≡ 0₂ ↦
                   ( π₁ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂)))
                 , t ≡ 1₂ ↦ m 1₂])
          , dhom2 B (v 0₂) (v 1₂) (w 1₂)
            ( v) (\ t → α₂ (t, 1₂)) (\ s → α₂ (s, s))
            ( \ (t, s) → α₂ (s, t))
            ( P) (f 0₂) (π₁ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂))) (m 1₂)
            ( \ s → (π₁ (π₂ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂)))) s) (h) (D))
        ( dhom2 B (v 0₂) (w 0₂) (w 1₂)
          ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
          ( \ ts → α₂ ts)
          ( P) (f 0₂) (m 0₂) (m 1₂)
          ( \ t → α₃ (t, 0₂)) (m) (D)))
      ( \ D → dhom2 B (v 0₂) (w 0₂) (w 1₂)
        ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
        ( \ ts → α₂ ts)
        ( P) (f 0₂) (m 0₂) (m 1₂)
        ( \ t → α₃ (t, 0₂)) (m) (D))
      ( \ D → equiv-product-is-contr
        ( Σ (h : (t : Δ¹) → P (α₂ (t, 1₂))
                 [ t ≡ 0₂ ↦
                   ( π₁ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂)))
                 , t ≡ 1₂ ↦ m 1₂])
          , dhom2 B (v 0₂) (v 1₂) (w 1₂)
            ( v) (\ t → α₂ (t, 1₂)) (\ s → α₂ (s, s))
            ( \ (t, s) → α₂ (s, t))
            ( P) (f 0₂) (π₁ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂))) (m 1₂)
            ( \ s → (π₁ (π₂ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂)))) s) (h) (D))
        ( dhom2 B (v 0₂) (w 0₂) (w 1₂)
          ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
          ( \ ts → α₂ ts)
          ( P) (f 0₂) (m 0₂) (m 1₂)
          ( \ t → α₃ (t, 0₂)) (m) (D))
        ( π₂
          ( π₂ (π₂ is-cocartesian-family-P (v 0₂) (v 1₂) (v) (f 0₂)))
          ( w 1₂) (\ t → α₂ (t, 1₂)) (\ t → α₂ (t, t)) (\ (t, s) → α₂ (s, t))
          ( D 1₂) D)))
    ( equiv-is-inverse
      ( Σ (D : dhom B (v 0₂) (w 1₂) (\ t → α₂ (t, t)) P (f 0₂) (m 1₂))
        , dhom2 B (v 0₂) (w 0₂) (w 1₂)
          ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
          ( \ ts → α₂ ts)
          ( P) (f 0₂) (m 0₂) (m 1₂)
          ( \ t → α₃ (t, 0₂)) (m) (D))
      ( ((t, s) : Δ²) → P (α₂ (t, s)) [s ≡ 0₂ ↦ α₃ (t, 0₂), t ≡ 1₂ ↦ m s])
      ( \ (_, τ) ts → τ ts)
      ( \ τ → (\ t → τ (t, t), \ ts → τ ts))
      ( \ _ → refl)
      ( \ _ → refl)))
  ( is-inner-family-P
    ( \ ts → α₂ ts)
    ( \ (t, s) → recOR(s ≡ 0₂ ↦ α₃ (t, 0₂), t ≡ 1₂ ↦ m s)))

#def has-enough-LARI-lifts-is-cocartesian-family
  ( B : U)
  ( P : B → U)
  ( is-cocartesian-family-P : is-cocartesian-family B P)
  : has-enough-LARI-lifts 2 Δ¹ (\ t → t ≡ 0₂) B P
  :=
  \ v f → ( π₁ (π₂ (π₂ (is-cocartesian-family-P) (v 0₂) (v 1₂) (v) (f 0₂)))
  , \ w m α₂ α₃ → is-contr-equiv-is-contr'
    ( ( (t, s) : 2 × 2 | Δ¹ t ∧ Δ¹ s) → P (α₂ (t, s))
      [ t ≡ 0₂ ↦
        ( π₁ (π₂ (π₂ (is-cocartesian-family-P) (v 0₂) (v 1₂) (v) (f 0₂)))) s
      , t ≡ 1₂ ↦ m s, s ≡ 0₂ ↦ α₃ (t, s)])
    ( Σ (D : dhom B (v 0₂) (w 1₂) (\ t → α₂ (t, t)) P (f 0₂) (m 1₂))
      , product
        ( Σ (h : (t : Δ¹) → P (α₂ (t, 1₂))
                  [ t ≡ 0₂ ↦
                    ( π₁ (π₂ (is-cocartesian-family-P) (v 0₂) (v 1₂) (v) (f 0₂)))
                  , t ≡ 1₂ ↦ m 1₂])
          , dhom2 B (v 0₂) (v 1₂) (w 1₂)
            ( v) (\ t → α₂ (t, 1₂)) (\ s → α₂ (s, s))
            ( \ (t, s) → α₂ (s, t))
            ( P) (f 0₂) (π₁ (π₂ (is-cocartesian-family-P) (v 0₂) (v 1₂) (v) (f 0₂))) (m 1₂)
            ( \ s → (π₁ (π₂ (π₂ (is-cocartesian-family-P) (v 0₂) (v 1₂) (v) (f 0₂)))) s) (h) (D))
        ( dhom2 B (v 0₂) (w 0₂) (w 1₂)
          ( \ t → α₂ (t, 0₂)) (w) (\ s → α₂ (s, s))
          ( \ ts → α₂ ts)
          ( P) (f 0₂) (m 0₂) (m 1₂)
          ( \ t → α₃ (t, 0₂)) (m) (D)))
    ( toname-equiv-4 B P v f
      ( π₁ (π₂ (π₂ (is-cocartesian-family-P) (v 0₂) (v 1₂) (v) (f 0₂))))
      ( w) m α₂ α₃)
    ( toname-contr B P
      ( π₁ (π₁ is-cocartesian-family-P))
      ( is-cocartesian-family-P) v f w m α₂ α₃))
```
