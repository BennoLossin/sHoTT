# LARI families

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#assume extext : ExtExt
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
    (g : X → B)
  → (f₀ : (y : Y) → P (g y))
  → has-initial ((x : X) → P (g x) [Y x ↦ f₀ x])
```

```rzk
#def is-LARI-family-has-transposing-LARI-adj-leibniz-cotensor
  ( B : U)
  ( P : B → U)
  ( is-segal-total-typ : is-segal (X → total-type B P))
  ( has-transposing-LARI-adj-leibniz-cotensor
    : has-transposing-LARI-adj
      ( X → total-type B P)
      ( leibniz-cotensor-codomain I X Y (total-type B P) B
        ( projection-total-type B P))
      ( is-segal-total-typ)
      ( leibniz-cotensor I X Y (total-type B P) B
        ( projection-total-type B P)))
  : is-LARI-family B P
  := TODO (is-LARI-family B P)
```

```rzk
#def has-transposing-LARI-adj-leibniz-cotensor-is-LARI-family
  ( B : U)
  ( P : B → U)
  ( is-segal-total-typ : is-segal (X → total-type B P))
  ( is-LARI-family-P : is-LARI-family B P)
  : has-transposing-LARI-adj
      ( X → total-type B P)
      ( leibniz-cotensor-codomain I X Y (total-type B P) B
        ( projection-total-type B P))
      ( is-segal-total-typ)
      ( leibniz-cotensor I X Y (total-type B P) B
        ( projection-total-type B P))
  :=
  TODO (has-transposing-LARI-adj
  ( X → total-type B P)
  ( leibniz-cotensor-codomain I X Y (total-type B P) B
    ( projection-total-type B P))
  ( is-segal-total-typ)
  ( leibniz-cotensor I X Y (total-type B P) B
    ( projection-total-type B P)))
```

```rzk title="BW23, Corollary 3.2.4"
#def is-LARI-family-orthogonal-to
  ( B : U)
  ( P : B → U)
  ( orthogonal-to-P : orthogonal-to I X Y B P)
  : is-LARI-family B P
  :=
  \ g f₀ → has-initial-is-contr extext
    ( (x : X) → P (g x) [Y x ↦ f₀ x])
    ( orthogonal-to-P g f₀)
```

```rzk
#end LARI-families
```
