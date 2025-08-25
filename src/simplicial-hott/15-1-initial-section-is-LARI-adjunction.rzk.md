# Dependent initial sections are LARI

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

##

Now we want to show that an initial section is transposing LARI. Firstly, we
show that it is a transposing adjunction:

```rzk
#def is-transposing-adj-is-dhom-initial-section
  ( A : U)
  ( B : A → U)
  ( s : (a : A) → B a)
  ( is-dhom-initial-section-s : is-dhom-initial-section A B s)
  : is-transposing-adj A (total-type A B)
  ( \ a → (a , s a))
  ( projection-total-type A B)
  := \ x (y , Y) → equiv-comp
  ( hom (total-type A B) (x , s x) (y , Y))
  ( Σ ( f : hom A x y) , dhom A x y f B (s x) Y)
  ( hom A x y)
  ( equiv-hom-sigma-dhom A B (x , s x) (y , Y))
  ( equiv-total-type-is-contr
    ( hom A x y)
    ( \ f → dhom A x y f B (s x) Y)
    ( is-dhom-initial-section-s x y Y))
```

```rzk
#def is-transposing-LARI-is-dhom-initial-section
  ( A : U)
  ( is-segal-A : is-segal A)
  ( B : A → U)
  ( s : (a : A) → B a)
  ( is-dhom-initial-section-s : is-dhom-initial-section A B s)
  : is-transposing-LARI A (total-type A B) is-segal-A (\ a → (a , s a))
  :=
  ( projection-total-type A B
  , ( is-transposing-adj-is-dhom-initial-section A B s is-dhom-initial-section-s
    , \ a → is-iso-arrow-id-hom A is-segal-A a))
```
