# The Yoneda lemma

These formalisations correspond to Section 9 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the axiom of function extensionality.
- `03-simplicial-type-theory.rzk.md` — We rely on definitions of simplicies and
  their subshapes.
- `04-extension-types.rzk.md` — We use the fubini theorem and extension
  extensionality.
- `05-segal-types.rzk.md` - We make heavy use of the notion of Segal types
- `08-covariant.rzk.md` - We use covariant type families.

Some of the definitions in this file rely on function extensionality and
extension extensionality:

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

## Natural transformations involving a representable functor

Fix a Segal type `#!rzk A` and a term `#!rzk a : A`. The Yoneda lemma
characterizes natural transformations from the representable type family
`#!rzk hom A a : A → U` to a covariant type family `#!rzk C : A → U`.

Ordinarily, such a natural transformation would involve a family of maps

`#!rzk ϕ : (z : A) → hom A a z → C z`

together with a proof of naturality of these components, but by
naturality-covariant-fiberwise-transformation naturality is automatic.

```rzk
#def naturality-covariant-fiberwise-representable-transformation
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x y : A)
  ( f : hom A a x)
  ( g : hom A x y)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( ϕ : (z : A) → hom A a z → C z)
  : ( covariant-transport A x y g C is-covariant-C (ϕ x f))
  = ( ϕ y (comp-is-segal A is-segal-A a x y f g))
  :=
    naturality-covariant-fiberwise-transformation A x y g
      ( \ z → hom A a z)
      ( C)
      ( is-covariant-representable-is-segal A is-segal-A a)
      ( is-covariant-C)
      ( ϕ)
      ( f)
```

## The Yoneda maps

For any Segal type `#!rzk A` and term `#!rzk a : A`, the Yoneda lemma provides
an equivalence between the type `#!rzk (z : A) → hom A a z → C z` of natural
transformations out of the functor `#!rzk hom A a` and values in an arbitrary
covariant family `#!rzk C` and the type `#!rzk C a`.

One of the maps in this equivalence is evaluation at the identity. The inverse
map makes use of the covariant transport operation.

The following map, `#!rzk evid`, evaluates a natural transformation out of a
representable functor at the identity arrow.

```rzk
#def evid
  ( A : U)
  ( a : A)
  ( C : A → U)
  : ( ( z : A) → hom A a z → C z) → C a
  := \ ϕ → ϕ a (id-hom A a)
```

The inverse map only exists for Segal types.

```rzk
#def yon
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  : C a → ((z : A) → hom A a z → C z)
  := \ u x f → covariant-transport A a x f C is-covariant-C u
```

## The Yoneda composites

It remains to show that the Yoneda maps are inverses. One retraction is
straightforward:

```rzk
#def evid-yon
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( u : C a)
  : ( evid A a C) ((yon A is-segal-A a C is-covariant-C) u) = u
  := id-arr-covariant-transport A a C is-covariant-C u
```

The other composite carries `#!rzk ϕ` to an a priori distinct natural
transformation. We first show that these are pointwise equal at all
`#!rzk x : A` and `#!rzk f : hom A a x` in two steps.

```rzk
#section yon-evid

#variable A : U
#variable is-segal-A : is-segal A
#variable a : A
#variable C : A → U
#variable is-covariant-C : is-covariant A C
```

The composite `#!rzk yon-evid` of `#!rzk ϕ` equals `#!rzk ϕ` at all
`#!rzk x : A` and `#!rzk f : hom A a x`.

```rzk
#def yon-evid-twice-pointwise
  ( ϕ : (z : A) → hom A a z → C z)
  ( x : A)
  ( f : hom A a x)
  : ( ( yon A is-segal-A a C is-covariant-C) ((evid A a C) ϕ)) x f = ϕ x f
  :=
    concat
      ( C x)
      ( ( ( yon A is-segal-A a C is-covariant-C) ((evid A a C) ϕ)) x f)
      ( ϕ x (comp-is-segal A is-segal-A a a x (id-hom A a) f))
      ( ϕ x f)
      ( naturality-covariant-fiberwise-representable-transformation
        A is-segal-A a a x (id-hom A a) f C is-covariant-C ϕ)
      ( ap
        ( hom A a x)
        ( C x)
        ( comp-is-segal A is-segal-A a a x (id-hom A a) f)
        ( f)
        ( ϕ x)
        ( id-comp-is-segal A is-segal-A a x f))
```

By `#!rzk funext`, these are equals as functions of `#!rzk f` pointwise in
`#!rzk x`.

```rzk
#def yon-evid-once-pointwise uses (funext)
  ( ϕ : (z : A) → hom A a z → C z)
  ( x : A)
  : ( ( yon A is-segal-A a C is-covariant-C) ((evid A a C) ϕ)) x = ϕ x
  :=
    eq-htpy funext
      ( hom A a x)
      ( \ f → C x)
      ( \ f → ((yon A is-segal-A a C is-covariant-C) ((evid A a C) ϕ)) x f)
      ( \ f → (ϕ x f))
      ( \ f → yon-evid-twice-pointwise ϕ x f)
```

By `#!rzk funext` again, these are equal as functions of `#!rzk x` and
`#!rzk f`.

```rzk
#def yon-evid uses (funext)
  ( ϕ : (z : A) → hom A a z → C z)
  : ( ( yon A is-segal-A a C is-covariant-C) ((evid A a C) ϕ)) = ϕ
  :=
    eq-htpy funext
      ( A)
      ( \ x → (hom A a x → C x))
      ( \ x → ((yon A is-segal-A a C is-covariant-C) ((evid A a C) ϕ)) x)
      ( \ x → (ϕ x))
      ( \ x → yon-evid-once-pointwise ϕ x)

#end yon-evid
```

## The Yoneda lemma

The Yoneda lemma says that evaluation at the identity defines an equivalence.
This is proven combining the previous steps.

```rzk title="RS17, Theorem 9.1"
#def yoneda-lemma uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  : is-equiv ((z : A) → hom A a z → C z) (C a) (evid A a C)
  :=
    ( ( ( yon A is-segal-A a C is-covariant-C)
      , ( yon-evid A is-segal-A a C is-covariant-C))
    , ( ( yon A is-segal-A a C is-covariant-C)
      , ( evid-yon A is-segal-A a C is-covariant-C)))
```

For later use, we observe that the same proof shows that the inverse map is an
equivalence.

```rzk
#def inv-yoneda-lemma uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  : is-equiv (C a) ((z : A) → hom A a z → C z)
      ( yon A is-segal-A a C is-covariant-C)
  :=
    ( ( ( evid A a C)
      , ( evid-yon A is-segal-A a C is-covariant-C))
    , ( ( evid A a C)
      , ( yon-evid A is-segal-A a C is-covariant-C)))
```

## Naturality

The equivalence of the Yoneda lemma is natural in both `#!rzk a : A` and
`#!rzk C : A → U`.

Naturality in `#!rzk a` follows from the fact that the maps `#!rzk evid` and
`#!rzk yon` are fiberwise equivalences between covariant families over
`#!rzk A`, though it requires some work to prove that the domain is covariant.

```rzk
#def is-covariant-yoneda-domain uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  : is-covariant A (\ a → (z : A) → hom A a z → C z)
  :=
    equiv-is-covariant
    ( extext)
    ( A)
    ( \ a → (z : A) → hom A a z → C z)
    ( C)
    ( \ a → (evid A a C , yoneda-lemma A is-segal-A a C is-covariant-C))
    ( is-covariant-C)

#def is-natural-in-object-evid uses (funext extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( f : hom A a b)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( ϕ : (z : A) → hom A a z → C z)
  : ( covariant-transport A a b f C is-covariant-C (evid A a C ϕ))
  = ( evid A b C

      ( covariant-transport A a b f
        ( \ x → (z : A) → hom A x z → C z)

        ( is-covariant-yoneda-domain A is-segal-A C is-covariant-C) ϕ))
  :=
    naturality-covariant-fiberwise-transformation
    ( A)
    ( a)
    ( b)
    ( f)
    ( \ x → (z : A) → hom A x z → C z)
    ( C)
    ( is-covariant-yoneda-domain A is-segal-A C is-covariant-C)
    ( is-covariant-C)
    ( \ x → evid A x C)
    ( ϕ)

#def is-natural-in-object-yon uses (funext extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( f : hom A a b)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( u : C a)
  : ( covariant-transport
      A a b f
      ( \ x → (z : A) → hom A x z → C z)
      ( is-covariant-yoneda-domain A is-segal-A C is-covariant-C)
      ( yon A is-segal-A a C is-covariant-C u))
  = ( yon A is-segal-A b C is-covariant-C
      ( covariant-transport A a b f C is-covariant-C u))
  :=
    naturality-covariant-fiberwise-transformation
    ( A)
    ( a)
    ( b)
    ( f)
    ( C)
    ( \ x → (z : A) → hom A x z → C z)
    ( is-covariant-C)
    ( is-covariant-yoneda-domain A is-segal-A C is-covariant-C)
    ( \ x → yon A is-segal-A x C is-covariant-C)
    ( u)
```

Naturality in `#!rzk C` is not automatic but can be proven easily:

```rzk title="RS17, Lemma 9.2(i)"
#def is-natural-in-family-evid
  ( A : U)
  ( a : A)
  ( C D : A → U)
  ( ψ : (z : A) → C z → D z)
  ( φ : (z : A) → hom A a z → C z)
  : ( comp ((z : A) → hom A a z → C z) (C a) (D a) (ψ a) (evid A a C)) φ
  = ( comp ((z : A) → hom A a z → C z) ((z : A) → hom A a z → D z) (D a)
    ( evid A a D) (\ α z g → ψ z (α z g))) φ
  := refl
```

```rzk title="RS17, Lemma 9.2(ii)"
#def is-natural-in-family-yon-twice-pointwise
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C D : A → U)
  ( is-covariant-C : is-covariant A C)
  ( is-covariant-D : is-covariant A D)
  ( ψ : (z : A) → C z → D z)
  ( u : C a)
  ( x : A)
  ( f : hom A a x)
  : ( comp (C a) (D a) ((z : A) → hom A a z → D z)
      ( yon A is-segal-A a D is-covariant-D) (ψ a)) u x f
  = ( comp (C a) ((z : A) → hom A a z → C z) ((z : A) → hom A a z → D z)
      ( \ α z g → ψ z (α z g)) (yon A is-segal-A a C is-covariant-C)) u x f
  :=
    naturality-covariant-fiberwise-transformation
      A a x f C D is-covariant-C is-covariant-D ψ u

#def is-natural-in-family-yon-once-pointwise uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C D : A → U)
  ( is-covariant-C : is-covariant A C)
  ( is-covariant-D : is-covariant A D)
  ( ψ : (z : A) → C z → D z)
  ( u : C a)
  ( x : A)
  : ( comp (C a) (D a) ((z : A) → hom A a z → D z)
      ( yon A is-segal-A a D is-covariant-D) (ψ a)) u x
  = ( comp (C a) ((z : A) → hom A a z → C z) ((z : A) → hom A a z → D z)
      ( \ α z g → ψ z (α z g)) (yon A is-segal-A a C is-covariant-C)) u x
  :=
    eq-htpy funext
      ( hom A a x)
      ( \ f → D x)
      ( \ f →
        ( comp (C a) (D a) ((z : A) → hom A a z → D z)
          ( yon A is-segal-A a D is-covariant-D) (ψ a)) u x f)
      ( \ f →
        ( comp (C a) ((z : A) → hom A a z → C z) ((z : A) → hom A a z → D z)
        ( \ α z g → ψ z (α z g)) (yon A is-segal-A a C is-covariant-C)) u x f)
      ( \ f →
        is-natural-in-family-yon-twice-pointwise
          A is-segal-A a C D is-covariant-C is-covariant-D ψ u x f)

#def is-natural-in-family-yon uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C D : A → U)
  ( is-covariant-C : is-covariant A C)
  ( is-covariant-D : is-covariant A D)
  ( ψ : (z : A) → C z → D z)
  ( u : C a)
  : ( comp (C a) (D a) ((z : A) → hom A a z → D z)
      ( yon A is-segal-A a D is-covariant-D) (ψ a)) u
  = ( comp (C a) ((z : A) → hom A a z → C z) ((z : A) → hom A a z → D z)
      ( \ α z g → ψ z (α z g)) (yon A is-segal-A a C is-covariant-C)) u
  :=
    eq-htpy funext
      ( A)
      ( \ x → hom A a x → D x)
      ( \ x →
        ( comp (C a) (D a) ((z : A) → hom A a z → D z)
          ( yon A is-segal-A a D is-covariant-D) (ψ a)) u x)
      ( \ x →
        ( comp (C a) ((z : A) → hom A a z → C z) ((z : A) → hom A a z → D z)
        ( \ α z g → ψ z (α z g)) (yon A is-segal-A a C is-covariant-C)) u x)
      ( \ x →
        is-natural-in-family-yon-once-pointwise
          A is-segal-A a C D is-covariant-C is-covariant-D ψ u x)
```

## Yoneda embedding.

```rzk title="Yoneda embedding. RS17, Definition 9.3"
#def yoneda-embedding
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a a' : A)
  : hom A a' a → (z : A) → hom A a z → hom A a' z
  :=
     yon
     ( A)
     ( is-segal-A)
     ( a)
     ( hom A a')
     ( is-covariant-representable-is-segal A is-segal-A a')

#def compute-yoneda-embedding-evid uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a a' : A)
  ( φ : (x : A) → (hom A a x → hom A a' x))
  : ( yoneda-embedding A is-segal-A a a') ((evid A a (hom A a')) φ) = φ
  :=
     yon-evid
      ( A)
      ( is-segal-A)
      ( a)
      ( hom A a')
      ( is-covariant-representable-is-segal A is-segal-A a') φ

#def htpy-compute-yoneda-embedding-evid uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a a' : A)
  ( φ : (x : A) → (hom A a x → hom A a' x))
  : ( x : A)
    → ( ( yoneda-embedding A is-segal-A a a') ((evid A a (hom A a')) φ)) x
    = φ x
  :=
     htpy-eq
      ( A)
      ( \ x → (hom A a x → hom A a' x))
      ( ( yoneda-embedding A is-segal-A a a') ((evid A a (hom A a')) φ))
      ( φ)
      ( compute-yoneda-embedding-evid A is-segal-A a a' φ)

#def htpy-yoneda-embedding-evid uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a a' : A)
  ( φ : (x : A) → (hom A a x → hom A a' x))
  ( x : A)
  : ( f : hom A a x)
    → ( ( yoneda-embedding A is-segal-A a a') ((evid A a (hom A a')) φ)) x f
    = φ x f
  :=
     htpy-eq
      ( hom A a x)
      ( \ z → hom A a' x)
      ( ( ( yoneda-embedding A is-segal-A a a')
          ( ( evid A a (hom A a')) φ)) x)
      ( φ x)
      ( htpy-compute-yoneda-embedding-evid A is-segal-A a a' φ x)

#def rev-compute-htpy-yoneda-embedding-evid uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a a' : A)
  ( φ : (x : A) → (hom A a x → hom A a' x))
  ( x : A)
  ( f : hom A a x)
  : φ x f
    = ( ( yoneda-embedding A is-segal-A a a') ((evid A a (hom A a')) φ)) x f
  :=
     rev
      ( hom A a' x)
      ( ( ( yoneda-embedding A is-segal-A a a')
          ( ( evid A a (hom A a')) φ)) x f)
      ( φ x f)
      ( htpy-yoneda-embedding-evid A is-segal-A a a' φ x f)
```

Define the action by precompostition.

```rzk
#def precomposition-evid-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a a' : A)
  ( φ : (x : A) → (hom A a x → hom A a' x))
  : ( x : A) → (hom A a x → hom A a' x)
  := \ x f → comp-is-segal A is-segal-A a' a x ((evid A a (hom A a')) φ) f
```

The Yoneda embedding coincides with `#!rzk precomposition-evid-is-segal`.

```rzk
#def eq-yoneda-embedding-precomposition-evid
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a a' : A)
  ( φ : (x : A) → (hom A a x → hom A a' x))
  ( x : A)
  ( f : hom A a x)
  : ( ( yoneda-embedding A is-segal-A a a') ((evid A a (hom A a')) φ)) x f
    = precomposition-evid-is-segal A is-segal-A a a' φ x f
  :=
     compute-covariant-transport-of-hom-family-is-segal
      ( A)
      ( is-segal-A)
      ( a')
      ( a)
      ( x)
      ( ( evid A a (hom A a')) φ)
      ( f)
```

Now we cocatenate the paths to prove the result as stated.

```rzk
#def eq-compute-precomposition-evid uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a a' : A)
  ( φ : (x : A) → (hom A a x → hom A a' x))
  ( x : A)
  ( f : hom A a x)
  : ( φ x) f = (precomposition-evid-is-segal A is-segal-A a a' φ x) f
  :=
     concat
      ( hom A a' x)
      ( φ x f)
      ( ( ( yoneda-embedding A is-segal-A a a')
          ( ( evid A a (hom A a')) φ)) x f)
      ( precomposition-evid-is-segal A is-segal-A a a' φ x f)
      ( rev-compute-htpy-yoneda-embedding-evid A is-segal-A a a' φ x f)
      ( eq-yoneda-embedding-precomposition-evid A is-segal-A a a' φ x f)

#def eq-htpy-precomposition-evid
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a a' : A)
  ( φ : (x : A) → (hom A a x → hom A a' x))
  ( x : A)
  : φ x = precomposition-evid-is-segal A is-segal-A a a' φ x
  :=
     eq-htpy
      ( funext)
      ( hom A a x)
      ( \ z → hom A a' x)
      ( φ x)
      ( precomposition-evid-is-segal A is-segal-A a a' φ x)
      ( \ f → eq-compute-precomposition-evid A is-segal-A a a' φ x f)

#def eq-precomposition-evid-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a a' : A)
  ( φ : (x : A) → (hom A a x → hom A a' x))
  : φ = precomposition-evid-is-segal A is-segal-A a a' φ
  :=
     eq-htpy
      ( funext)
      ( A)
      ( \ x → (hom A a x → hom A a' x))
      ( φ)
      ( precomposition-evid-is-segal A is-segal-A a a' φ)
      ( \ x → eq-htpy-precomposition-evid A is-segal-A a a' φ x)
```

## Yoneda for contravariant families

Dually, the Yoneda lemma for contravariant type families characterizes natural
transformations from the contravariant family represented by a term
`#!rzk a : A` in a Segal type to a contravariant type family `#!rzk C : A → U`.

By `#!rzk naturality-contravariant-fiberwise-transformation` naturality is again
automatic.

```rzk
#def naturality-contravariant-fiberwise-representable-transformation
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x y : A)
  ( f : hom A y a)
  ( g : hom A x y)
  ( C : A → U)
  ( is-contravariant-C : is-contravariant A C)
  ( ϕ : (z : A) → hom A z a → C z)
  : ( contravariant-transport A x y g C is-contravariant-C (ϕ y f))
  = ( ϕ x (comp-is-segal A is-segal-A x y a g f))
  :=
    naturality-contravariant-fiberwise-transformation A x y g
      ( \ z → hom A z a) C
      ( is-contravariant-representable-is-segal A is-segal-A a)
      ( is-contravariant-C)
      ( ϕ)
      ( f)
```

For any Segal type `#!rzk A` and term `#!rzk a : A`, the contravariant Yoneda
lemma provides an equivalence between the type `#!rzk (z : A) → hom A z a → C z`
of natural transformations out of the functor `#!rzk \ z → hom A z a` and valued
in an arbitrary contravariant family `#!rzk C` and the type `#!rzk C a`.

One of the maps in this equivalence is evaluation at the identity. The inverse
map makes use of the contravariant transport operation.

The following map, `#!rzk contra-evid` evaluates a natural transformation out of
a representable functor at the identity arrow.

```rzk
#def contra-evid
  ( A : U)
  ( a : A)
  ( C : A → U)
  : ( ( z : A) → hom A z a → C z) → C a
  := \ ϕ → ϕ a (id-hom A a)
```

The inverse map only exists for Segal types and contravariant families.

```rzk
#def contra-yon
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C : A → U)
  ( is-contravariant-C : is-contravariant A C)
  : C a → ((z : A) → hom A z a → C z)
  := \ v z f → contravariant-transport A z a f C is-contravariant-C v
```

It remains to show that the Yoneda maps are inverses. One retraction is
straightforward:

```rzk
#def contra-evid-yon
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C : A → U)
  ( is-contravariant-C : is-contravariant A C)
  ( v : C a)
  : contra-evid A a C ((contra-yon A is-segal-A a C is-contravariant-C) v) = v
  := id-arr-contravariant-transport A a C is-contravariant-C v
```

The other composite carries `#!rzk ϕ` to an a priori distinct natural
transformation. We first show that these are pointwise equal at all
`#!rzk x : A` and `#!rzk f : hom A x a` in two steps.

```rzk
#section contra-yon-evid

#variable A : U
#variable is-segal-A : is-segal A
#variable a : A
#variable C : A → U
#variable is-contravariant-C : is-contravariant A C
```

The composite `#!rzk contra-yon-evid` of `#!rzk ϕ` equals `#!rzk ϕ` at all
`#!rzk x : A` and `#!rzk f : hom A x a`.

```rzk
#def contra-yon-evid-twice-pointwise
  ( ϕ : (z : A) → hom A z a → C z)
  ( x : A)
  ( f : hom A x a)
  : ( ( contra-yon A is-segal-A a C is-contravariant-C)
        ( ( contra-evid A a C) ϕ)) x f = ϕ x f
  :=
    concat
      ( C x)
      ( ( ( contra-yon A is-segal-A a C is-contravariant-C)
            ( ( contra-evid A a C) ϕ)) x f)
      ( ϕ x (comp-is-segal A is-segal-A x a a f (id-hom A a)))
      ( ϕ x f)
      ( naturality-contravariant-fiberwise-representable-transformation
          A is-segal-A a x a (id-hom A a) f C is-contravariant-C ϕ)
      ( ap
        ( hom A x a)
        ( C x)
        ( comp-is-segal A is-segal-A x a a f (id-hom A a))
        ( f)
        ( ϕ x)
        ( comp-id-is-segal A is-segal-A x a f))
```

By `#!rzk funext`, these are equals as functions of `#!rzk f` pointwise in
`#!rzk x`.

```rzk
#def contra-yon-evid-once-pointwise uses (funext)
  ( ϕ : (z : A) → hom A z a → C z)
  ( x : A)
  : ( ( contra-yon A is-segal-A a C is-contravariant-C)
        ( ( contra-evid A a C) ϕ)) x = ϕ x
  :=
    eq-htpy funext
      ( hom A x a)
      ( \ f → C x)
      ( \ f →
        ( ( contra-yon A is-segal-A a C is-contravariant-C)
          ( ( contra-evid A a C) ϕ)) x f)
      ( \ f → (ϕ x f))
      ( \ f → contra-yon-evid-twice-pointwise ϕ x f)
```

By `#!rzk funext` again, these are equal as functions of `#!rzk x` and
`#!rzk f`.

```rzk
#def contra-yon-evid uses (funext)
  ( ϕ : (z : A) → hom A z a → C z)
  : contra-yon A is-segal-A a C is-contravariant-C (contra-evid A a C ϕ) = ϕ
  :=
    eq-htpy funext
      ( A)
      ( \ x → (hom A x a → C x))
      ( contra-yon A is-segal-A a C is-contravariant-C (contra-evid A a C ϕ))
      ( ϕ)
      ( contra-yon-evid-once-pointwise ϕ)

#end contra-yon-evid
```

The contravariant Yoneda lemma says that evaluation at the identity defines an
equivalence.

```rzk
#def contra-yoneda-lemma uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C : A → U)
  ( is-contravariant-C : is-contravariant A C)
  : is-equiv ((z : A) → hom A z a → C z) (C a) (contra-evid A a C)
  :=
    ( ( ( contra-yon A is-segal-A a C is-contravariant-C)
      , ( contra-yon-evid A is-segal-A a C is-contravariant-C))
    , ( ( contra-yon A is-segal-A a C is-contravariant-C)
      , ( contra-evid-yon A is-segal-A a C is-contravariant-C)))
```

For later use, we observe that the same proof shows that the inverse map is an
equivalence.

```rzk
#def inv-contra-yoneda-lemma uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C : A → U)
  ( is-contravariant-C : is-contravariant A C)
  : is-equiv (C a) ((z : A) → hom A z a → C z)
      ( contra-yon A is-segal-A a C is-contravariant-C)
  :=
    ( ( ( contra-evid A a C)
      , ( contra-evid-yon A is-segal-A a C is-contravariant-C))
    , ( ( contra-evid A a C)
      , ( contra-yon-evid A is-segal-A a C is-contravariant-C)))
```

## Contravariant naturality

The equivalence of the Yoneda lemma is natural in both `#!rzk a : A` and
`#!rzk C : A → U`.

Naturality in `#!rzk a` follows from the fact that the maps `#!rzk evid` and
`#!rzk yon` are fiberwise equivalences between contravariant families over
`#!rzk A`, though it requires some work, which has not yet been formalized, to
prove that the domain is contravariant.

Naturality in `#!rzk C` is not automatic but can be proven easily:

```rzk title="RS17, Lemma 9.2(i), dual"
#def is-natural-in-family-contra-evid
  ( A : U)
  ( a : A)
  ( C D : A → U)
  ( ψ : (z : A) → C z → D z)
  ( φ : (z : A) → hom A z a → C z)
  : ( comp ((z : A) → hom A z a → C z) (C a) (D a)
      ( ψ a) (contra-evid A a C)) φ
  = ( comp ((z : A) → hom A z a → C z) ((z : A) → hom A z a → D z) (D a)
      ( contra-evid A a D) (\ α z g → ψ z (α z g))) φ
  := refl
```

```rzk title="RS17, Lemma 9.2(ii), dual"
#def is-natural-in-family-contra-yon-twice-pointwise
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C D : A → U)
  ( is-contravariant-C : is-contravariant A C)
  ( is-contravariant-D : is-contravariant A D)
  ( ψ : (z : A) → C z → D z)
  ( u : C a)
  ( x : A)
  ( f : hom A x a)
  : ( comp (C a) (D a) ((z : A) → hom A z a → D z)
      ( contra-yon A is-segal-A a D is-contravariant-D) (ψ a)) u x f
  = ( comp (C a) ((z : A) → hom A z a → C z) ((z : A) → hom A z a → D z)
      ( \ α z g → ψ z (α z g))
      ( contra-yon A is-segal-A a C is-contravariant-C)) u x f
  :=
    naturality-contravariant-fiberwise-transformation
      A x a f C D is-contravariant-C is-contravariant-D ψ u

#def is-natural-in-family-contra-yon-once-pointwise uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C D : A → U)
  ( is-contravariant-C : is-contravariant A C)
  ( is-contravariant-D : is-contravariant A D)
  ( ψ : (z : A) → C z → D z)
  ( u : C a)
  ( x : A)
  : ( comp (C a) (D a) ((z : A) → hom A z a → D z)
      ( contra-yon A is-segal-A a D is-contravariant-D) (ψ a)) u x
  = ( comp (C a) ((z : A) → hom A z a → C z) ((z : A) → hom A z a → D z)
      ( \ α z g → ψ z (α z g))
      ( contra-yon A is-segal-A a C is-contravariant-C)) u x
  :=
    eq-htpy funext
      ( hom A x a)
      ( \ f → D x)
      ( \ f →
        ( comp (C a) (D a) ((z : A) → hom A z a → D z)
          ( contra-yon A is-segal-A a D is-contravariant-D) (ψ a)) u x f)
      ( \ f →
        ( comp (C a) ((z : A) → hom A z a → C z) ((z : A) → hom A z a → D z)
        ( \ α z g → ψ z (α z g))
        ( contra-yon A is-segal-A a C is-contravariant-C)) u x f)
      ( \ f →
        is-natural-in-family-contra-yon-twice-pointwise
          A is-segal-A a C D is-contravariant-C is-contravariant-D ψ u x f)

#def is-natural-in-family-contra-yon uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C D : A → U)
  ( is-contravariant-C : is-contravariant A C)
  ( is-contravariant-D : is-contravariant A D)
  ( ψ : (z : A) → C z → D z)
  ( u : C a)
  : ( comp (C a) (D a) ((z : A) → hom A z a → D z)
      ( contra-yon A is-segal-A a D is-contravariant-D) (ψ a)) u
  = ( comp (C a) ((z : A) → hom A z a → C z) ((z : A) → hom A z a → D z)
      ( \ α z g → ψ z (α z g))
      ( contra-yon A is-segal-A a C is-contravariant-C)) u
  :=
    eq-htpy funext
      ( A)
      ( \ x → hom A x a → D x)
      ( \ x →
        ( comp (C a) (D a) ((z : A) → hom A z a → D z)
          ( contra-yon A is-segal-A a D is-contravariant-D) (ψ a)) u x)
      ( \ x →
        ( comp (C a) ((z : A) → hom A z a → C z) ((z : A) → hom A z a → D z)
        ( \ α z g → ψ z (α z g))
        ( contra-yon A is-segal-A a C is-contravariant-C)) u x)
      ( \ x →
        is-natural-in-family-contra-yon-once-pointwise
          A is-segal-A a C D is-contravariant-C is-contravariant-D ψ u x)
```

From a type-theoretic perspective, the Yoneda lemma is a “directed” version of
the “transport” operation for identity types. This suggests a “dependently
typed” generalization of the Yoneda lemma, analogous to the full induction
principle for identity types. We prove this as a special case of a result about
covariant families over a type with an initial object.

## Initial objects

A term `#!rzk a` in a type `#!rzk A` is initial if all of its mapping-out hom
types are contractible.

```rzk title="RS17, Definition 9.6"
#def is-initial
  ( A : U)
  ( a : A)
  : U
  := (x : A) → is-contr (hom A a x)
```

Initial objects map to initial objects by equivalences.

```rzk
#def is-inital-equiv-is-initial uses (extext)
  ( A B : U)
  ( e : Equiv A B)
  ( a : A)
  ( is-initial-a : is-initial A a)
  :
  is-initial B (first e a)
  :=
  \ b →
    ind-has-section-equiv A B e
      ( \ b → is-contr (hom B (first e a) b))
      ( \ a' → is-contr-equiv-is-contr (hom A a a')
          ( hom B (first e a) (first e a'))
          ( ap-hom A B (first e) a a'
          , is-equiv-ap-hom-is-equiv extext A B (first e) (second e) a a')
      ( is-initial-a a'))
      ( b)
```

Initial objects satisfy an induction principle relative to covariant families.

```rzk
#section initial-evaluation-equivalence

#variable A : U
#variable a : A
#variable is-initial-a : is-initial A a
#variable C : A → U
#variable is-covariant-C : is-covariant A C

#def arrows-from-initial
  ( x : A)
  : hom A a x
  := center-contraction (hom A a x) (is-initial-a x)

#def identity-component-arrows-from-initial
  : arrows-from-initial a = id-hom A a
  := homotopy-contraction (hom A a a) (is-initial-a a) (id-hom A a)

#def ind-initial uses (is-initial-a)
  ( u : C a)
  : ( x : A) → C x
  :=
    \ x → covariant-transport A a x (arrows-from-initial x) C is-covariant-C u

#def has-cov-section-ev-pt uses (is-initial-a)
  : has-section ((x : A) → C x) (C a) (ev-pt A a C)
  :=
    ( ( ind-initial)
    , ( \ u →
        concat
          ( C a)
          ( covariant-transport A a a
            ( arrows-from-initial a) C is-covariant-C u)
          ( covariant-transport A a a
            ( id-hom A a) C is-covariant-C u)
          ( u)
          ( ap
            ( hom A a a)
            ( C a)
            ( arrows-from-initial a)
            ( id-hom A a)
            ( \ f →
              covariant-transport A a a f C is-covariant-C u)
            ( identity-component-arrows-from-initial))
          ( id-arr-covariant-transport A a C is-covariant-C u)))

#def ind-initial-ev-pt-pointwise uses (is-initial-a)
  ( s : (x : A) → C x)
  ( b : A)
  : ind-initial (ev-pt A a C s) b = s b
  :=
    covariant-uniqueness
      ( A)
      ( a)
      ( b)
      ( arrows-from-initial b)
      ( C)
      ( is-covariant-C)
      ( ev-pt A a C s)
      ( ( s b , \ t → s (arrows-from-initial b t)))

#end initial-evaluation-equivalence
```

We now prove that induction from an initial element in the base of a covariant
family defines an inverse equivalence to evaluation at the element.

```rzk title="RS17, Theorem 9.7"
#def is-equiv-covariant-ev-initial uses (funext)
  ( A : U)
  ( a : A)
  ( is-initial-a : is-initial A a)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  : is-equiv ((x : A) → C x) (C a) (ev-pt A a C)
  :=
    ( ( ( ind-initial A a is-initial-a C is-covariant-C)
      , ( \ s → eq-htpy
                  funext
                    ( A)
                    ( C)
                    ( ind-initial
                        A a is-initial-a C is-covariant-C (ev-pt A a C s))
                    ( s)
                    ( ind-initial-ev-pt-pointwise
                        A a is-initial-a C is-covariant-C s)))
    , ( has-cov-section-ev-pt A a is-initial-a C is-covariant-C))
```

### Useful alternative definition of `is-initial`

```rzk
#def is-initial2
  ( A : U)
  ( a : A)
  : U
  := Σ (f : (y : A) → hom A a y) , f a = id-hom A a
```

This definition is equivalent to `is-initial`.

```rzk
#def is-initial2-is-initial
  ( A : U)
  ( x : A)
  ( is-initial-x : is-initial A x)
  : is-initial2 A x
  :=
  ( \ y → center-contraction (hom A x y) (is-initial-x y)
  , homotopy-contraction (hom A x x) (is-initial-x x) (id-hom A x))
```

The inverse is much more complicated and also requires that `A` is Segal:

```rzk
#def is-initial-is-initial2-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x : A)
  ( is-initial2-x : is-initial2 A x)
  : is-initial A x
  :=
  \ (y : A) → (
    π₁ is-initial2-x y
  , \ (f : hom A x y) →
      rev
        ( hom A x y)
        f
        ( π₁ is-initial2-x y)
        ( quadruple-concat
          ( hom A x y)
          f
          ( comp-is-segal A is-segal-A x x y (id-hom A x) f)
          ( comp-is-segal A is-segal-A x x y (π₁ is-initial2-x x) f)
          ( comp-is-segal A is-segal-A x x y (id-hom A x) (π₁ is-initial2-x y))
          ( π₁ is-initial2-x y)
          ( rev
            ( hom A x y)
            ( comp-is-segal A is-segal-A x x y (id-hom A x) f)
            f
            ( id-comp-is-segal A is-segal-A x y f))
          ( ap
            ( hom A x x)
            ( hom A x y)
            ( id-hom A x)
            ( π₁ is-initial2-x x)
            ( \ g → comp-is-segal A is-segal-A x x y g f)
            ( rev (hom A x x) (π₁ is-initial2-x x) (id-hom A x) (π₂ is-initial2-x)))
          ( rev
            ( hom A x y)
            ( comp-is-segal A is-segal-A x x y (id-hom A x) (π₁ is-initial2-x y))
            ( comp-is-segal A is-segal-A x x y (π₁ is-initial2-x x) f)
            ( naturality-nat-trans-is-segal
              A A
              is-segal-A
              ( constant A A x) (identity A)
              ( nat-trans-nat-trans-components A (\ _ → A) (constant A A x) (identity A) (π₁ is-initial2-x))
              x y
              f))
          ( id-comp-is-segal A is-segal-A x y (π₁ is-initial2-x y))))
```

### Initial objects and embeddings

```rzk
#assume TODO : (A : U) → A

#def is-initial-is-emb
  ( A B : U)
  ( f : A → B)
  ( is-emb-f : is-emb A B f)
  ( a : A)
  ( is-initial-fa : is-initial B (f a))
  : is-initial A a
  :=
  is-prop-is-emb-is-prop
```

## Initial objects in slice categories

Recall that the type `#!rzk coslice A a` is the type of arrows in `#!rzk A` with
domain `#!rzk a`.

We now show that the coslice under `#!rzk a` in a Segal type `#!rzk A` has an
initial object given by the identity arrow at `#!rzk a`. This makes use of the
following equivalence.

```rzk
#def equiv-hom-in-coslice
  ( A : U)
  ( a x : A)
  ( f : hom A a x)
  : Equiv
    ( hom (coslice A a) (a , id-hom A a) (x , f))
    ( ( t : Δ¹) → hom A a (f t) [t ≡ 0₂ ↦ id-hom A a])
  :=
    ( \ h t s → (second (h s)) t
    , ( ( \ k s → (k 1₂ s , \ t → k t s)
      , \ h → refl)
    , ( \ k s → (k 1₂ s , \ t → k t s)
      , \ k → refl)))
```

Since `#!rzk hom A a` is covariant when `#!rzk A` is Segal, this latter type is
contractible.

```rzk
#def is-contr-is-segal-hom-in-coslice
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x : A)
  ( f : hom A a x)
  : is-contr ((t : Δ¹) → hom A a (f t) [t ≡ 0₂ ↦ id-hom A a])
  :=
    ( second (has-unique-fixed-domain-lifts-iff-is-covariant
                A (\ z → hom A a z)))
      ( is-covariant-representable-is-segal A is-segal-A a)
      ( a)
      ( x)
      ( f)
      ( id-hom A a)
```

This proves the initiality of identity arrows in the coslice of a Segal type.

```rzk title="RS17, Lemma 9.8"
#def is-initial-id-hom-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  : is-initial (coslice A a) (a , id-hom A a)
  :=
    \ (x , f) →
    is-contr-equiv-is-contr'
      ( hom (coslice A a) (a , id-hom A a) (x , f))
      ( ( t : Δ¹) → hom A a (f t) [t ≡ 0₂ ↦ id-hom A a])
      ( equiv-hom-in-coslice A a x f)
      ( is-contr-is-segal-hom-in-coslice A is-segal-A a x f)
```

## Dependent Yoneda lemma

The dependent Yoneda lemma now follows by specializing these results.

```rzk
#def dependent-evid
  ( A : U)
  ( a : A)
  ( C : (coslice A a) → U)
  : ( ( p : coslice A a) → C p) → C (a , id-hom A a)
  := \ s → s (a , id-hom A a)

#def dependent-yoneda-lemma' uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C : (coslice A a) → U)
  ( is-covariant-C : is-covariant (coslice A a) C)
  : is-equiv
      ( ( p : coslice A a) → C p)
      ( C (a , id-hom A a))
      ( dependent-evid A a C)
  :=
    is-equiv-covariant-ev-initial
      ( coslice A a)
      ( ( a , id-hom A a))
      ( is-initial-id-hom-is-segal A is-segal-A a)
      ( C)
      ( is-covariant-C)
```

The actual dependent Yoneda is equivalent to the result just proven, just with
an equivalent type in the domain of the evaluation map.

```rzk title="RS17, Theorem 9.5"
#def dependent-yoneda-lemma uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C : (coslice A a) → U)
  ( is-covariant-C : is-covariant (coslice A a) C)
  : is-equiv
      ( ( x : A) → (f : hom A a x) → C (x , f))
      ( C (a , id-hom A a))
      ( \ s → s a (id-hom A a))
  :=
    is-equiv-left-factor
      ( ( p : coslice A a) → C p)
      ( ( x : A) → (f : hom A a x) → C (x , f))
      ( C (a , id-hom A a))
      ( first (equiv-dependent-curry A (\ z → hom A a z) (\ x f → C (x , f))))
      ( second (equiv-dependent-curry A (\ z → hom A a z) (\ x f → C (x , f))))
      ( \ s → s a (id-hom A a))
      ( dependent-yoneda-lemma' A is-segal-A a C is-covariant-C)
```

## Final objects

A term `#!rzk a` in a type `#!rzk A` is initial if all of its mapping-out hom
types are contractible.

```rzk
#def is-final
  ( A : U)
  ( a : A)
  : U
  := (x : A) → is-contr (hom A x a)
```

Final objects map to final objects by equivalences.

```rzk
#def is-final-equiv-is-final uses (extext)
  ( A B : U)
  ( e : Equiv A B)
  ( a : A)
  ( is-final-a : is-final A a)
  :
  is-final B (first e a)
  :=
  \ b →
    ind-has-section-equiv A B e
      ( \ b → is-contr (hom B b (first e a)))
      ( \ a' → is-contr-equiv-is-contr (hom A a' a)
          ( hom B (first e a') (first e a))
          ( ap-hom A B (first e) a' a
          , is-equiv-ap-hom-is-equiv extext A B (first e) (second e) a' a)
      ( is-final-a a'))
      ( b)
```

Final objects satisfy an induction principle relative to contravariant families.

```rzk
#section final-evaluation-equivalence

#variable A : U
#variable a : A
#variable is-final-a : is-final A a
#variable C : A → U
#variable is-contravariant-C : is-contravariant A C

#def arrows-to-final
  ( x : A)
  : hom A x a
  := center-contraction (hom A x a) (is-final-a x)

#def identity-component-arrows-to-final
  : arrows-to-final a = id-hom A a
  := homotopy-contraction (hom A a a) (is-final-a a) (id-hom A a)

#def ind-final uses (is-final-a)
  ( u : C a)
  : ( x : A) → C x
  :=
    \ x →
    contravariant-transport A x a (arrows-to-final x) C is-contravariant-C u

#def has-contra-section-ev-pt uses (is-final-a)
  : has-section ((x : A) → C x) (C a) (ev-pt A a C)
  :=
    ( ( ind-final)
    , ( \ u →
        concat
          ( C a)
          ( contravariant-transport A a a
            ( arrows-to-final a) C is-contravariant-C u)
          ( contravariant-transport A a a
            ( id-hom A a) C is-contravariant-C u)
          ( u)
          ( ap
            ( hom A a a)
            ( C a)
            ( arrows-to-final a)
            ( id-hom A a)
            ( \ f →
              contravariant-transport A a a f C is-contravariant-C u)
            ( identity-component-arrows-to-final))
          ( id-arr-contravariant-transport A a C is-contravariant-C u)))

#def ind-final-ev-pt-pointwise uses (is-final-a)
  ( s : (x : A) → C x)
  ( b : A)
  : ind-final (ev-pt A a C s) b = s b
  :=
    contravariant-uniqueness
      ( A)
      ( b)
      ( a)
      ( arrows-to-final b)
      ( C)
      ( is-contravariant-C)
      ( ev-pt A a C s)
      ( ( s b , \ t → s (arrows-to-final b t)))

#end final-evaluation-equivalence
```

We now prove that induction from a final element in the base of a contravariant
family defines an inverse equivalence to evaluation at the element.

```rzk title="RS17, Theorem 9.7, dual"
#def is-equiv-contravariant-ev-final uses (funext)
  ( A : U)
  ( a : A)
  ( is-final-a : is-final A a)
  ( C : A → U)
  ( is-contravariant-C : is-contravariant A C)
  : is-equiv ((x : A) → C x) (C a) (ev-pt A a C)
  :=
    ( ( ( ind-final A a is-final-a C is-contravariant-C)
      , ( \ s → eq-htpy
                  funext
                    ( A)
                    ( C)
                    ( ind-final
                        A a is-final-a C is-contravariant-C (ev-pt A a C s))
                    ( s)
                    ( ind-final-ev-pt-pointwise
                        A a is-final-a C is-contravariant-C s)))
    , ( has-contra-section-ev-pt A a is-final-a C is-contravariant-C))
```

### Useful alternative definition of `is-final`

```rzk
#def is-final2
  ( A : U)
  ( a : A)
  : U
  := Σ (f : (x : A) → hom A x a) , f a = id-hom A a
```

This definition is equivalent to `is-final`.

```rzk
#def is-final2-is-final
  ( A : U)
  ( y : A)
  ( is-final-y : is-final A y)
  : is-final2 A y
  :=
  ( \ x → center-contraction (hom A x y) (is-final-y x)
  , homotopy-contraction (hom A y y) (is-final-y y) (id-hom A y))
```

The inverse is much more complicated and also requires that `A` is Segal:

```rzk
#def is-final-is-final2
  ( A : U)
  ( is-segal-A : is-segal A)
  ( y : A)
  ( is-final2-y : is-final2 A y)
  : is-final A y
  :=
  \ (x : A) → (
    π₁ is-final2-y x
  , \ (f : hom A x y) →
      rev
        ( hom A x y)
        f
        ( π₁ is-final2-y x)
        ( quadruple-concat
          ( hom A x y)
          f
          ( comp-is-segal A is-segal-A x y y f (id-hom A y))
          ( comp-is-segal A is-segal-A x y y f (π₁ is-final2-y y))
          ( comp-is-segal A is-segal-A x y y (π₁ is-final2-y x) (id-hom A y))
          ( π₁ is-final2-y x)
          ( rev
            ( hom A x y)
            ( comp-is-segal A is-segal-A x y y f (id-hom A y))
            f
            ( comp-id-is-segal A is-segal-A x y f))
          ( ap
            ( hom A y y)
            ( hom A x y)
            ( id-hom A y)
            ( π₁ is-final2-y y)
            ( \ g → comp-is-segal A is-segal-A x y y f g)
            ( rev (hom A y y) (π₁ is-final2-y y) (id-hom A y) (π₂ is-final2-y)))
          ( naturality-nat-trans-is-segal
            A A
            is-segal-A
            ( identity A) (constant A A y)
            ( nat-trans-nat-trans-components A (\ _ → A) (identity A) (constant A A y) (π₁ is-final2-y))
            x y
            f)
          ( comp-id-is-segal A is-segal-A x y (π₁ is-final2-y x))))
```

Finally, we prove the equivalence:

```rzk
#def iff-is-segal-TOBEBIKESHED
  ( A : U)
  ( is-segal-A : is-segal A)
  ( y : A)
  : iff (is-final A y) (is-final2 A y)
  := (is-final2-is-final A y , is-final-is-final2 A is-segal-A y)
```

## Final objects in slice categories

Recall that the type `#!rzk slice A a` is the type of arrows in `#!rzk A` with
codomain `#!rzk a`.

We now show that the slice over `#!rzk a` in a Segal type `#!rzk A` has a final
object given by the identity arrow at `#!rzk a`. This makes use of the following
equivalence.

```rzk
#def equiv-hom-in-slice
  ( A : U)
  ( a x : A)
  ( f : hom A x a)
  : Equiv
    ( hom (slice A a) (x , f) (a , id-hom A a))
    ( ( t : Δ¹) → hom A (f t) a [t ≡ 1₂ ↦ id-hom A a])
  :=
    ( \ h t s → (second (h s)) t
    , ( ( \ k s → (k 0₂ s , \ t → k t s)
      , \ h → refl)
    , ( \ k s → (k 0₂ s , \ t → k t s)
      , \ k → refl)))
```

Since `#!rzk \ z → hom A z a` is contravariant when `#!rzk A` is Segal, this
latter type is contractible.

```rzk
#def is-contr-is-segal-hom-in-slice
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x : A)
  ( f : hom A x a)
  : is-contr ((t : Δ¹) → hom A (f t) a [t ≡ 1₂ ↦ id-hom A a])
  :=
    ( second (has-unique-fixed-codomain-lifts-iff-is-contravariant
                A (\ z → hom A z a)))
      ( is-contravariant-representable-is-segal A is-segal-A a)
      ( x)
      ( a)
      ( f)
      ( id-hom A a)
```

This proves the finality of identity arrows in the slice of a Segal type.

```rzk title="RS17, Lemma 9.8, dual"
#def is-final-id-hom-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  : is-final (slice A a) (a , id-hom A a)
  :=
    \ (x , f) →
    is-contr-equiv-is-contr'
      ( hom (slice A a) (x , f) (a , id-hom A a))
      ( ( t : Δ¹) → hom A (f t) a [t ≡ 1₂ ↦ id-hom A a])
      ( equiv-hom-in-slice A a x f)
      ( is-contr-is-segal-hom-in-slice A is-segal-A a x f)
```

## Contravariant Dependent Yoneda lemma

The contravariant version of the dependent Yoneda lemma now follows by
specializing these results.

```rzk
#def contra-dependent-evid
  ( A : U)
  ( a : A)
  ( C : (slice A a) → U)
  : ( ( p : slice A a) → C p) → C (a , id-hom A a)
  := \ s → s (a , id-hom A a)

#def contra-dependent-yoneda-lemma' uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C : (slice A a) → U)
  ( is-contravariant-C : is-contravariant (slice A a) C)
  : is-equiv
      ( ( p : slice A a) → C p)
      ( C (a , id-hom A a))
      ( contra-dependent-evid A a C)
  :=
    is-equiv-contravariant-ev-final
      ( slice A a)
      ( ( a , id-hom A a))
      ( is-final-id-hom-is-segal A is-segal-A a)
      ( C)
      ( is-contravariant-C)
```

The actual contravariant dependent Yoneda is equivalent to the result just
proven, just with an equivalent type in the domain of the evaluation map.

```rzk title="RS17, Theorem 9.5, dual"
#def contra-dependent-yoneda-lemma uses (funext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  ( C : (slice A a) → U)
  ( is-contravariant-C : is-contravariant (slice A a) C)
  : is-equiv
      ( ( x : A) → (f : hom A x a) → C (x , f))
      ( C (a , id-hom A a))
      ( \ s → s a (id-hom A a))
  :=
    is-equiv-left-factor
      ( ( p : slice A a) → C p)
      ( ( x : A) → (f : hom A x a) → C (x , f))
      ( C (a , id-hom A a))
      ( first (equiv-dependent-curry A (\ z → hom A z a) (\ x f → C (x , f))))
      ( second (equiv-dependent-curry A (\ z → hom A z a) (\ x f → C (x , f))))
      ( \ s → s a (id-hom A a))
      ( contra-dependent-yoneda-lemma'
          A is-segal-A a C is-contravariant-C)
```

## Representable Families

A covariant family is representable if it is fiberweise equivalent to covariant
homs. In order to check if this is the case, it is not necessary to know if the
family is covariant or not.

```rzk
#def is-representable-family
  ( A : U)
  ( C : A → U)
  : U
  := Σ (a : A) , (x : A) → (Equiv (hom A a x) (C x))
```

The definition makes it slightly awkward to access the actual equivalence, so we
give a helper function.

```rzk
#def equiv-for-is-representable-family
  ( A : U)
  ( C : A → U)
  ( is-rep-C : is-representable-family A C)
  : ( x : A) → (hom A (first is-rep-C) x) → (C x)
  := \ x → first((second (is-rep-C)) x)
```

RS Proposition 9.10 gives an if and only if condition for a covariant family
`#!rzk C : A → U` to be representable. The condition is that the type
`#!rzk Σ (x : A) , C x` has an initial object. For convenience, we give this
condition a name.

```rzk
#def has-initial-tot
  ( A : U)
  ( C : A → U)
  : U
  := Σ ((a , u) : Σ (x : A) , (C x))
      , is-initial (Σ (x : A) , (C x)) (a , u)
```

As a representable family is fiberwise equivalent to a `#!rzk Σ (x : A) , C x`,
the total space of the family is equivalent to a coslice, and coslices have an
initial object by `#!rzk is-initial-id-hom-is-segal`.

```rzk
#def has-initial-tot-is-representable-family uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( C : A → U)
  ( is-rep-C : is-representable-family A C)
  : has-initial-tot A C
  :=
    ( ( first is-rep-C
      , evid
          ( A)
          ( first is-rep-C)
          ( C)
          ( equiv-for-is-representable-family A C is-rep-C))
    , is-inital-equiv-is-initial
        ( coslice A (first is-rep-C))
        ( Σ ( x : A) , (C x))
        ( total-equiv-family-of-equiv
          ( A)
          ( \ x → hom A (first is-rep-C) x)
          ( C)
          ( second is-rep-C))
        ( ( first is-rep-C , id-hom A (first is-rep-C)))
        ( is-initial-id-hom-is-segal A is-segal-A (first is-rep-C)))

```

The other direction is a bit longer. We follow the proof of RS17 9.10: given
`#!rzk (a, u) : Σ (x : A) , C x` an initial object of `#!rzk Σ (x : A) , C x`,
evaluating `#!rzk yon` at `#!rzk u : C a` yields a family of maps
`#!rzk (x : A) → hom A a x → C x`. This is a contractible map as its fiber at
`#!rzk (b : A, v : C b)` is equivalent to the hom type
`#!rzk hom (Σ (x : A) , C x) (a, u) (b, v)` through the composite of
`#!rzk covariant-uniqueness-curried` and `#!rzk axiom-choice` and it is thus an
equivalence using `#!rzk is-equiv-is-contr-map`.

```rzk
#def is-representable-family-has-initial-tot
  ( A : U)
  ( is-segal-A : is-segal A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( has-initial-tot-A : has-initial-tot A C)
  : ( is-representable-family A C)
  :=
    ( first (first has-initial-tot-A)
    , \ b →
      ( ( yon
          ( A)
          ( is-segal-A)
          ( first (first has-initial-tot-A))
          ( C)
          ( is-covariant-C)
          ( second (first has-initial-tot-A))
          ( b))
      , is-equiv-is-contr-map
        ( hom A (first (first has-initial-tot-A)) b)
        ( C b)
        ( yon
          ( A)
          ( is-segal-A)
          ( first (first has-initial-tot-A))
          ( C)
          ( is-covariant-C)
          ( second (first has-initial-tot-A))
          ( b))
        ( \ v →
          is-contr-equiv-is-contr
            ( hom (Σ (a : A) , (C a)) (first has-initial-tot-A) (b , v))
            ( fib
                ( hom A (first (first has-initial-tot-A)) b)
                ( C b)
                ( yon
                  ( A)
                  ( is-segal-A)
                  ( first (first has-initial-tot-A))
                  ( C)
                  ( is-covariant-C)
                  ( second (first has-initial-tot-A))
                  ( b))
                ( v))
            ( equiv-comp
              ( hom (Σ (a : A) , (C a)) (first has-initial-tot-A) (b , v))
              ( Σ ( f : hom A (first (first has-initial-tot-A)) b)
                , dhom
                  ( A)
                  ( first (first has-initial-tot-A))
                  ( b)
                  ( f)
                  ( C)
                  ( second (first has-initial-tot-A))
                  ( v))
              ( fib
                ( hom A (first (first has-initial-tot-A)) b)
                ( C b)
                ( yon
                  ( A)
                  ( is-segal-A)
                  ( first (first has-initial-tot-A))
                  ( C)
                  ( is-covariant-C)
                  ( second (first has-initial-tot-A))
                  ( b))
                ( v))
              ( axiom-choice
                    ( 2)
                    ( Δ¹)
                    ( ∂Δ¹)
                    ( \ _ → A)
                    ( \ t x → C x)
                    ( \ t →
                      recOR
                        ( t ≡ 0₂ ↦ first (first has-initial-tot-A)
                        , t ≡ 1₂ ↦ b))
                    ( \ t →
                      recOR
                        ( t ≡ 0₂ ↦ second (first has-initial-tot-A)
                        , t ≡ 1₂ ↦ v)))
              ( total-equiv-family-of-equiv
                ( hom A (first (first has-initial-tot-A)) b)
                ( \ f →
                  dhom
                    ( A)
                    ( first (first has-initial-tot-A))
                    ( b)
                    ( f)
                    ( C)
                    ( second (first has-initial-tot-A))
                    ( v))
                ( \ f →
                  covariant-transport
                    ( A)
                    ( first (first has-initial-tot-A))
                    ( b)
                    ( f)
                    ( C)
                    ( is-covariant-C)
                    ( second (first has-initial-tot-A))
                  = v)
                ( \ f →
                    ( covariant-uniqueness-curried
                      ( A)
                      ( first (first has-initial-tot-A))
                      ( b)
                      ( f)
                      ( C)
                      ( is-covariant-C)
                      ( second (first has-initial-tot-A))
                      ( v)
                    , is-equiv-covariant-uniqueness-curried
                      ( A)
                      ( first (first has-initial-tot-A))
                      ( b)
                      ( f)
                      ( C)
                      ( is-covariant-C)
                      ( second (first has-initial-tot-A))
                      ( v)))))
            ( second has-initial-tot-A (b , v)))))
```

```rzk title="RS17, Proposition 9.10"
#def is-representable-iff-has-initial-tot uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  : iff (is-representable-family A C) (has-initial-tot A C)
  :=
    ( \ is-rep-C →
      has-initial-tot-is-representable-family
      ( A)
      ( is-segal-A)
      ( C)
      ( is-rep-C)
    , \ has-initial-tot-A →
      is-representable-family-has-initial-tot
      ( A)
      ( is-segal-A)
      ( C)
      ( is-covariant-C)
      ( has-initial-tot-A))
```
