# Pullbacks of LARI families

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#def is-LARI-cell
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( B : U)
  ( P : B → U)
  ( v : ψ → B)
  ( g : (t : ψ) → P (v t))
  : U
  :=
    ( w : ψ → B)
  → ( m : (t : ψ) → P (w t))
  → ( α₂ : ((t, s) : 2 × I | Δ¹ t ∧ ψ s) → B [t ≡ 0₂ ↦ v s, t ≡ 1₂ ↦ w s])
  → ( α₃ : ((t, s) : 2 × I | Δ¹ t ∧ ϕ s) → P (α₂ (t, s)) [t ≡ 0₂ ↦ g s, t ≡ 1₂ ↦ m s])
  → is-contr (
    ( (t, s) : 2 × I | Δ¹ t ∧ ψ s) → P (α₂ (t, s))
    [ t ≡ 0₂ ↦ g s, t ≡ 1₂ ↦ m s, ϕ s ↦ α₃ (t, s)])
```

```rzk
#def has-enough-LARI-lifts
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( B : U)
  ( P : B → U)
  : U
  :=
    ( v : ψ → B)
  → ( f : (t : ϕ) → P (u t))
  → Σ ( g : (t : ψ) → P (v t) [ϕ t → f t]) , is-LARI-cell I ψ ϕ B P v g
```
