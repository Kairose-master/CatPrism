# ε-Approximate Functor

This document describes CatPrism's notion of an approximate functor.

## ε-Identity compatibility

From this version each `EpsFunctor` also checks how identity maps
are preserved.  The generator inserts a proof stub

```lean
id_ok := by verify_id
```

so downstream proofs can rely on the functor being close to identity
on objects and morphisms.
