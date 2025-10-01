# Cocartesian Fibrations

```rzk
#lang rzk-1
```

```rzk
#assume TODO : (A : U) → A
```

## Cocartesian Arrows

```rzk
#def Δ¹₁
  : Δ¹ → TOPE
  := \ t → t ≡ 0₂
```


```rzk
#variable B : U
#variable P : B → U

#def dependent-compositions-are-horn-fillings
  ( b b' : B)
  ( u : hom B b b')
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  ( e'' : P b')
  ( h : dhom B b b' u P e e'')
  : Equiv
    ( Σ ( g : dhom B b' b' (id-hom B b') P e' e'')
    , ( dhom2 B b b' b' u (id-hom B b') u (\ (s, t) → u s) P e e' e'' f g h))
    ( hom ((t : Δ¹) → P (u t) [t ≡ 0₂ ↦ e]) f h)
  :=
  equiv-is-inverse
  ( Σ ( g : dhom B b' b' (id-hom B b') P e' e'')
  , ( dhom2 B b b' b' u (id-hom B b') u (\ (s, t) → u s) P e e' e'' f g h))
  ( hom ((t : Δ¹) → P (u t) [t ≡ 0₂ ↦ e]) f h)
  ( \ (_ , σ) s t → recOR(s ≤ t ↦ σ (t, s), t ≤ s ↦ h t))
  ( \ H → transport
    ( dhom B b b' u P e e'')
    ( \ F → (((t, s) : Δ²) → P (u t) [t ≡ s ↦ F t, s ≡ 0₂ ↦ f t]))
    ( \ t → H (t, t))
    ( h)
    ( TODO (
    ( \ t → H (t, t))
    =
    ( h)
    )
    )
    ( H)
    )
  ( \ _ → refl)
  ( \ _ → refl)

#def is-LARI-family-is-cocartesian-family
  ( is-cocartesian-family-P : is-cocartesian-family B P)
  : is-LARI-family 2 Δ¹ Δ¹₁ B P
  :=
  \ (g : Δ¹ → B) (f₀ : (t : Δ¹₁) → P (g t)) →
  ( π₁ (π₂ (π₂ is-cocartesian-family-P (g 0₂) (g 1₂) g (f₀ 0₂)))
  , \ F → π₂ (π₂ (π₂ is-cocartesian-family-P (g 0₂) (g 1₂) (g) (f₀ 0₂)))
    ( g 1₂) (id-hom B (g 1₂)) (g) (TODO) (F 1₂) (F)
  )
  -- has-initial ((t: Δ¹) → P (g t) [Δ¹₁ t ↦ f₀ t])

#def is-cocartesian-family-is-LARI-family-is-isoinner-family
  ( is-isoinner-family-P : is-isoinner-family B P)
  ( is-LARI-family-P : is-LARI-family 2 Δ¹ Δ¹₁ B P)
  : is-cocartesian-family B P
  :=
  ( is-isoinner-family-P
  , \ b b' u e → (π₁ (is-LARI-family-P u (\ _ → e)) 1₂
    , ( π₁ (is-LARI-family-P u (\ _ → e))
      , TODO)))

#def is-cocartesian-family-iff-leibniz-LARI-is-isoinner
  ( is-isoinner-family-P : is-isoinner-family B P)
  : iff
    ( is-cocartesian-family B P)
    ( is-LARI-family 2 Δ¹ Δ¹₁ B P)
  :=
  TODO (iff
    ( is-cocartesian-family B P)
    ( is-LARI-family 2 Δ¹ Δ¹₁ B P))
```
