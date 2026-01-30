# Cocartesian families

These formalizations capture cocartesian families as treated in BW23.

The goal, for now, is not to give a general structural account as in the paper
but rather to provide the definitions and results that are necessary to prove
the cocartesian Yoneda Lemma.

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
- `10-rezk-types.rzk.md`- We use Rezk types.

