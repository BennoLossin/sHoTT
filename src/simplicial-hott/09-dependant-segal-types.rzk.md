# Dependent Segal Types

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Dependent segal condition

Analogously to the independant segal condition, the dependant segal condition
asks for uniqueness of composition of dependant morphisms.

```rzk
#def is-dsegal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( B : A → U)
  : U
  :=
    ( x : A) → (y : A) → (z : A)
  → ( f : hom A x y) → (g : hom A y z)
  → ( X : B x) → (Y : B y) → (Z : B z)
  → ( F : dhom A x y f B X Y) → (G : dhom A y z g B Y Z)
  → is-contr
    ( Σ ( H : dhom A x z (comp-is-segal A is-segal-A x y z f g) B X Z)
    , dhom2
      A x y z f g (comp-is-segal A is-segal-A x y z f g)
      ( witness-comp-is-segal A is-segal-A x y z f g)
      B X Y Z F G H)
```

Using this, we can define dependant composition.

```rzk
#def dcomp-is-dsegal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( B : A → U)
  ( is-dsegal-B : is-dsegal A is-segal-A B)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( X : B x)
  ( Y : B y)
  ( Z : B z)
  ( F : dhom A x y f B X Y)
  ( G : dhom A y z g B Y Z)
  : dhom A x z (comp-is-segal A is-segal-A x y z f g) B X Z
  := π₁ (π₁ (is-dsegal-B x y z f g X Y Z F G))
```

```rzkk
#def is-equiv-dcomp-is-contr-is-dsegal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( B : A → U)
  ( is-dsegal-B : is-dsegal A is-segal-A B)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( X : B x)
  ( Y : B y)
  ( Z : B z)
  ( is-contr-dhom : is-contr (dhom A x y f B X Y))
  : is-equiv
  ( dhom y z f B Y Z)
  ( dhom A x z (comp-is-segal A is-segal-A x y z f g) B X Z)
  ( \ G → dcomp-is-dsegal
    ( A) is-segal-A B is-dsegal-B x y z f g X Y Z (π₁ is-contr-dhom) G)
  :=

```

## Total type

The total type of a dependant segal type is segal.

```rzk
#section is-segal-total-type-is-dsegal

#variable A : U
#variable is-segal-A : is-segal A
#variable B : A → U
#variable is-dsegal-B : is-dsegal A is-segal-A B

#def center-total-type-is-dsegal
  ( x : total-type A B)
  ( y : total-type A B)
  ( z : total-type A B)
  ( f : hom (total-type A B) x y)
  ( g : hom (total-type A B) y z)
  : Σ ( h : hom (total-type A B) x z)
  , hom2 (total-type A B) x y z f g h
  :=
  ( hom-sigma-dhom A B x z
    ( comp-is-segal A is-segal-A (π₁ x) (π₁ y) (π₁ z)
      ( π₁ (sigma-dhom-hom A B x y f))
      ( π₁ (sigma-dhom-hom A B y z g))
    , π₁ (π₁ (is-dsegal-B
      ( π₁ x) (π₁ y) (π₁ z)
      ( π₁ (sigma-dhom-hom A B x y f))
      ( π₁ (sigma-dhom-hom A B y z g))
      ( π₂ x) (π₂ y) (π₂ z)
      ( π₂ (sigma-dhom-hom A B x y f))
      ( π₂ (sigma-dhom-hom A B y z g)))))
  , hom2-sigma-dhom2 A B x y z f g
    ( hom-sigma-dhom A B x z
      ( comp-is-segal A is-segal-A (π₁ x) (π₁ y) (π₁ z)
        ( π₁ (sigma-dhom-hom A B x y f))
        ( π₁ (sigma-dhom-hom A B y z g))
      , π₁ (π₁ (is-dsegal-B
        ( π₁ x) (π₁ y) (π₁ z)
        ( π₁ (sigma-dhom-hom A B x y f))
        ( π₁ (sigma-dhom-hom A B y z g))
        ( π₂ x) (π₂ y) (π₂ z)
        ( π₂ (sigma-dhom-hom A B x y f))
        ( π₂ (sigma-dhom-hom A B y z g))))))
    ( π₂ (π₁ (is-segal-A (π₁ x) (π₁ y) (π₁ z)
      ( π₁ (sigma-dhom-hom A B x y f))
      ( π₁ (sigma-dhom-hom A B y z g))))
    , π₂ (π₁ (is-dsegal-B
      ( π₁ x) (π₁ y) (π₁ z)
      ( π₁ (sigma-dhom-hom A B x y f))
      ( π₁ (sigma-dhom-hom A B y z g))
      ( π₂ x) (π₂ y) (π₂ z)
      ( π₂ (sigma-dhom-hom A B x y f))
      ( π₂ (sigma-dhom-hom A B y z g))))))

#def is-segal-total-type-is-dsegal uses (is-segal-A is-dsegal-B)
  : is-segal (total-type A B)
  := \ x y z f g →
  ( center-total-type-is-dsegal x y z f g
  , \ cc → TODO (center-total-type-is-dsegal x y z f g = cc))

#end is-segal-total-type-is-dsegal
```

## Homotopies

Similar to independant segal types, homotopies between parallel morphisms are
terms in dhom2 involving an identity arrow. To shorten notation, we introduce a
name for this concept.

```rzk
#def dhom-hpty
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( B : A → U)
  ( X : B x)
  ( Y : B y)
  ( F G : dhom A x y f B X Y)
  : U
  :=
  dhom2
    A x x y (id-hom A x) f f (id-comp-witness A x y f)
    B X X Y (id-dhom A x B X) F G
```

Any function is homotopic to itself.

```rzk
#def id-dcomp-witness
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( B : A → U)
  ( X : B x)
  ( Y : B y)
  ( F : dhom A x y f B X Y)
  : dhom-hpty A x y f B X Y F F
  := \ (t₁ , t₂) → F t₂
```

And equal morphisms are homotopic.

```rzk
#def map-dhom2-homotopy
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( B : A → U)
  ( X : B x)
  ( Y : B y)
  ( F G : dhom A x y f B X Y)
  : ( F = G) → (dhom-hpty A x y f B X Y F G)
  :=
  ind-path
    ( dhom A x y f B X Y)
    ( F)
    ( \ G' p → (dhom-hpty A x y f B X Y F G'))
    ( id-dcomp-witness A x y f B X Y F)
    ( G)
```

Now we prepare to show that in a dependant segal type, the notion of equality on
morphisms is equivalent to the notion of homotopy. The same proof idea used for
segal types also works here, adapted for the dependant context.

```rzk
#def map-total-dhom2-homotopy
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( B : A → U)
  ( X : B x)
  ( Y : B y)
  ( F : dhom A x y f B X Y)
  : ( Σ ( G : dhom A x y f B X Y) , F = G)
  → ( Σ ( G : dhom A x y f B X Y) , dhom-hpty A x y f B X Y F G)
  := \ (G , p) → (G , map-dhom2-homotopy A x y f B X Y F G p)
```
