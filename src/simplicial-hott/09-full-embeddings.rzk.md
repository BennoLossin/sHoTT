# Full Embeddings

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#assume TODO : (A : U) → A
```

##

```rzk
#section full-embeddings

#variables A B : U
#variable f : A → B

#def is-full-emb
  : U
  :=
  product
  ( is-emb A B f)
  ( (x : A)
  → (y : A)
  → is-equiv (hom A x y) (hom B (f x) (f y)) (ap-hom A B x y f))
```

### Full Embeddings are Embeddings

```rzk
#def
```

```rzk
#def is-emb-is-full-emb
  : is-emb f
  := \ x y → TODO (is-equiv (x = y) (f x = f y) (ap A B x y f))
```
