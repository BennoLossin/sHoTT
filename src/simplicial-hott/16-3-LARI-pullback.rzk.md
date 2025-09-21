# Pullbacks of LARI families

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#def is-LARI-family-pullback
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( A B : U)
  ( P : B → U)
  ( k : A → B)
  ( is-LARI-family-P : is-LARI-family I X Y B P)
  : is-LARI-family I X Y A (\ a → P (k a))
  := \ g f₀ → is-LARI-family-P (\ x → k (g x)) (\ y → f₀ y)
```
