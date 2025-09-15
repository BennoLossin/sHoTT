# LARI families

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#assume TODO : (A : U) → A
```


## LARI families

```rzk
#section LARI-families

#variable I : CUBE
#variable X : I → TOPE
#variable Y : X → TOPE
```

```rzk title="BW23, Definition 3.2.2"
#def is-LARI-family
  ( B : U)
  ( P : B → U)
  : U
  :=
    (g₀ : Y → B)
  → (f₀ : (y : Y) → P (g₀ y))
  → (g : (x : X) → B [Y x ↦ g₀ x])
  → has-initial ((x : X) → P (g x) [Y x ↦ f₀ x])
```

```rzk title="BW23, Corollary 3.2.4"
#def is-LARI-family-orthogonal-to
  ( B : U)
  ( P : B → U)
  ( orthogonal-to-P : orthogonal-to I X Y B P)
  : is-LARI-family B P
  := TODO (is-LARI-family B P)
```

```rzk
#end LARI-families
```
