# CatPrism v0.1.0 — "Prismatic Genesis"

*17 June 2025*

---

## 🌈 Highlights

- **Core DSL** — `.cat` grammar for categories, functors, custom metrics (`Δθ | Δlen | Δzero`) and ε‑composition rule.
- **Rust Parser + CLI** — `catprism` binary: `parse --input foo.cat --output foo.cat.ast.json`, `export-lean`, full AST (JSON) output.
- **Lean Proof Engine** — `verify_comp` tactic, `derive_phase` meta‑tactic, `PhaseDist` & `LengthDist` metrics, `HasLength` framework.
- **Web Renderer** — Mermaid graph + WebGL beams with ε‑hue encoding; drop‑in `renderCatPrism` ESM module.
- **CI Pipeline** — GitHub Actions: Rust build/tests → `.cat` → `.lean` export → Lean proofs + fmt checks.
- **MIT + Ethical Clause** — permissive licence with anti‑harm pledge.

---

## 🆕 Files & Folders

```
README.md, LICENSE, CONTRIBUTING.md
.github/workflows/lean-ci.yml
spec/syntax.cat
parser/ (Rust crate)
core/lean/Core.lean + examples
renderer/catprism-render.mjs
examples/Projection1.cat / .ast.json + Example2~4.cat
```

---

## 🧪 Examples

- **Projection1** — Vec/Mat → Display (Δθ, ε = 0.15)
- **Matrix Phase** — Mat → U(1) (Δθ, ε = 0.3)
- **Forgetful** — Groups → Sets (Δzero)
- **Shape Compare** — Δθ vs Δlen metrics side‑by‑side

Run:

```bash
catprism parse --input examples/Projection1.cat --output examples/Projection1.cat.ast.json
catprism export-lean --input examples/Projection1.cat
lake build          # inside core/lean
```

---

## 🚧 Known Limitations

- Δlen metric proof uses simplistic `‖z‖` length; richer path‑lengths WIP.
- Renderer beam animation is linear; Bézier & ε‑slider planned.
- VS Code syntax highlight / playground not yet packaged.

---

## 💡 Roadmap → v0.2.0

1. **Parser UX** — better error spans, Unicode identifiers.
2. **Profunctor support** — Bidirectional projections.
3. **Web Playground** — WASM parser + live Lean proof check.
4. **VS Code Extension** — .cat highlight, proof status bar.

---

*🖋 Released by Jinwoo & Lua — "도구를 쓰지 말고, 구조와 함께 걸어라."*

