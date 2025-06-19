# 🐱🌈 CatPrism

**Category‑Theoretic Prism DSL · Rust × Lean × WebGL**

> _“GPT는 기억하지 않는다. 그러나 함께할 수는 있다.”_  
> — *CatPrism Philosophy*

CatPrism is an open‑source toolchain for **ε‑tolerant functorial projections**: write category/functor specs in a concise `.cat` DSL, _prove_ composition‑preservation in Lean, _visualise_ the projection beams in the browser, and export runtime evaluators in Rust/Haskell.

---

## ✨ Key Features

| Layer | Tech | What it does |
|-------|------|--------------|
| **DSL** | `.cat` files | `category`, `functor`, `distortion_metric`, `ε‑rule` |
| **Parser** | Rust `nom` + `serde` | AST JSON ↔ Lean export |
| **Proof** | Lean4 | `verify_comp` tactic, `derive_phase`, `LengthDist`, `PhaseDist` |
| **Visual** | Mermaid + WebGL | Interactive graph + colour‑coded distortion beams |
| **CI** | GitHub Actions | `.cat → .lean → lake build` proof check |

---

## 📦 Repository Layout

```
CatPrism/
├── spec/              # DSL grammar & docs
├── core/
│   ├── lean/          # Lean library (Category, metrics, tactics)
│   └── haskell/       # Runtime evaluator (stub)
├── parser/            # Rust crate (`catprism` CLI)
│   ├── src/
│   └── templates/
├── renderer/          # Mermaid + WebGL overlay (ESM)
├── examples/          # *.cat, *.ast.json, *.lean
└── docs/              # White‑papers & blog drafts
```

---

## 🚀 Quick Start

### 1 · Build prerequisites

* **Rust 1.75+** (`rustup install stable`)
* **Node 18+** (for browser demo)
* **Lean 4** via `elan` (`elan toolchain install 4.3.0`)  
  `lake` will be installed automatically.

### 2 · Clone & compile

```bash
$ git clone https://github.com/your‑handle/CatPrism.git
$ cd CatPrism/parser
$ cargo build --release
```

### 3 · Parse & proof

```bash
# JSON AST for renderer
$ ./target/release/catprism parse --json ../examples/Projection1.cat

# Lean proof export
$ ./target/release/catprism export-lean --input ../examples/Projection1.cat
$ cd ../core/lean && lake build
```

### 4 · Visualise

```bash
$ cd ../renderer
$ python -m http.server 9000
# open http://localhost:9000/demo.html
```

---

## 🧪 Examples

* **Example 2** — Matrix → Phase (Δθ, ε = 0.3)  
* **Example 3** — Groups → Sets (Δzero, ε = 0)  
* **Example 4** — Shape → Display with Δθ / Δlen comparison

Run `catprism export-lean --input examples/ExampleX.cat` then `lake build` to verify.

---

## 🤝 Contributing
Pull requests are welcome! Interesting entry points:

* `parser/` — improve error reporting, Unicode identifiers
* `core/lean/` — new metrics, tactics, profunctor support
* `renderer/` — beam animation, ε slider UI, VS Code Webview

Please read `CONTRIBUTING.md` for coding style & DCO sign‑off.

---

## 🛡️ License

CatPrism is released under the **MIT License**.  
See `LICENSE` for details plus an additional *Ethical Use Clause*:  
> _“Use CatPrism to build systems of understanding, not systems of harm.”_

---

## 🌱 Acknowledgements
*Created by **Jinwoo** (author) and **Lua** (the cat‑prism companion).*  
Special thanks to the category‑theory community & the open‑source ecosystem.

> _“도구를 쓰지 말고, 구조와 함께 걸어라.”_  
> _— Chapter 1, forthcoming series_

```markdown
### ⚠️ Inference Collapse — Logged Error & Attempt Summary

#### 🔥 Error Log (Lean 4.21.0-rc2)

error: application type mismatch:
  ?m ≫ F.map g
expected: ?m ⟶ ?m

error: Core.lean:38:37:
  F.map g has type:
    F.obj B ⟶ F.obj C₁ : Type ?u
  but is expected to have type:
    ?m f g ⟶ ?m f g : Type ?u

error: Core.lean:55:27:
  invalid argument name 'd' for function

Lean exited with code 1

- Lean version: leanprover/lean4 v4.21.0-rc2
- mathlib commit: 2025-06-14
- File: Core.lean (DSL structure: EpsFunctor)

---

#### 🧪 Attempted Fixes & Structural Results

| Attempt                                  | Result | Note                                                  |
|------------------------------------------|--------|--------------------------------------------------------|
| Used `F.map f ≫ F.map g` manually         | ✅ Pass | Inference succeeds manually                           |
| Used `F.map (g ≫ f)` inside DSL           | ❌ Fail | Metavariable collapse: `?m ≫ F.map g`                 |
| Simplified DSL structure (`EpsFunctor`)   | ❌ Fail | Same inference failure                                |
| Explicit Category instance annotations    | ❌ Fail | No effect — inference fails regardless                |
| Internal metric structures (`HasPhase`)   | ✅ Pass | No issue with isolated morphism structure             |

---

#### 🧠 Diagnosis

- Lean’s elaborator fails to resolve source/target category when `F.map (g ≫ f)` appears **inside DSL-structured contexts**.
- Instead of resolving the morphism types, it **falls back to metavariables** and produces `application type mismatch`.
- This is not a syntactic issue but a **structural limitation** in how Lean infers composed morphisms across DSLs.

---

#### 🧬 Example DSL Structure

structure EpsFunctor (...) where
  F : C ⥤ D
  comp_ok :
    ∀ f g, d (F.map (g ≫ f)) ((F.map f) ≫ (F.map g)) ≤ ε
```

