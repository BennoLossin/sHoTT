# Cocartesian Fibrations

```rzk
#lang rzk-1
```

```rzk
#assume TODO : (A : U) → A
```

## Cocartesian Arrows

```rzk
#def is-cocartesian-family-iff-leibniz-LARI-is-isoinner
  ( B : U)
  ( P : B → U)
  ( is-isoinner-family-P : is-isoinner-family B P)
  : iff
    ( is-cocartesian-family B P)
    ( is-LARI-family 2 Δ¹ (\ t → t ≡ 0₂) B P)
  :=
  TODO (iff
    ( is-cocartesian-family B P)
    ( is-LARI-family 2 Δ¹ (\ t → t ≡ 0₂) B P))
```
