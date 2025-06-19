# Internal Development Note: Extending `EpsFunctor` with Identity Compatibility

**Author:** Jinwoo Jang (CatPrismOS)  
**Based on suggestions by:** Joël Riou (Lean core category theory contributor)  
**Date:** 2025-06-19

---

## 1. Summary

The current version of `EpsFunctor` defines approximate composition preservation via a metric:

```lean
structure EpsFunctor where
  F : C ⥤ D
  comp_ok : ∀ f g, d (F.map (g ≫ f)) ((F.map f) ≫ (F.map g)) ≤ ε
```

However, as noted by Joël Riou, if `F` is a functor, then `F.map (g ≫ f)` = `F.map g ≫ F.map f`, making the distance zero by functoriality. Thus, a non-zero distance metric only makes sense in a *non-functorial* setting such as `Prefunctor`, or under a relaxed notion of functoriality.

In addition, he suggests adding **compatibility with identity morphisms**:

> "It would probably make sense to add a compatibility with identities as well as with compositions."

This document sketches an internal development direction to include identity compatibility.

---

## 2. Goal

Extend the `EpsFunctor` structure to:

- Include a condition for **identity preservation up to ε** (or δ metric)
- Optionally allow `F` to be a **Prefunctor** (without assuming full functoriality)
- Enable future DSL flexibility for enriched categories

---

## 3. Design Sketch

### 3.1 Additional Field

```lean
id_ok : ∀ A, d (F.map (𝟙 A)) (𝟙 (F.obj A)) ≤ ε
```

This asserts that `F.map` is approximately identity-preserving.

### 3.2 Total Updated Structure

```lean
structure EpsFunctor where
  F : C ⥤ D
  comp_ok : ∀ f g, d (F.map (g ≫ f)) ((F.map f) ≫ (F.map g)) ≤ ε
  id_ok   : ∀ A, d (F.map (𝟙 A)) (𝟙 (F.obj A)) ≤ ε
```

---

## 4. Future Considerations

- Define `Prefunctor` structure explicitly in DSL layer (if not importing from mathlib)
- Explore generalization of `d` as a family of morphism-based pseudometrics (e.g., `d_comp`, `d_id`)
- Consider epsilon-bounded transformations (`∀ f, d (F.map f) (G.map f) ≤ ε`) for DSL equivalences

---

## 5. Appendix: Joël's Original Insight

> "As you assume that F is a functor, so that F.map (f ≫ g) = F.map f ≫ F.map g, then for any reasonable metric, the distance should be zero. [...] It would probably make sense to add a compatibility with identities as well as with compositions."

---

Thank you so much again — really appreciate your time and insight! ☺️
