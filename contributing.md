# Contributing to CatPrism

Thanks for your interest in making CatPrism better! 🐱🌈\
Below are a few guidelines to help us work together smoothly.

---

## 📜 Code of Conduct

We follow the [Contributor Covenant](https://www.contributor-covenant.org/).\
Be kind, respectful, and assume good intent.

---

## 🛠️ Project Structure

```
core/lean/     Lean proofs + tactics
parser/        Rust CLI & AST handling
renderer/      Browser visualiser (Mermaid+WebGL)
examples/      *.cat specs + auto‑generated *.lean / *.json
spec/          DSL grammar docs
```

---

## 🚀 Getting Started

1. `git clone` & `cd CatPrism`
2. **Rust**: `cargo build -p catprism`  (parser CLI)\
   **Lean**: `lake build` inside `core/lean`
3. Run tests: `cargo test` + `lake build`.

---

## 🐛 Issues & Feature Requests

Submit an issue with:

1. **Title**: concise summary.
2. **Describe**: reproduction steps or feature motivation.
3. **Label**: `bug`, `enhancement`, `doc`, `question`.

---

## 💻 Pull Requests

### Branch Naming

`feature/<area>-<desc>` · `fix/<area>-<bug>` · `docs/<desc>`

### Checklist

-

### Sign‑off (DCO)

Add to each commit message:

```
Signed-off-by: Your Name <you@example.com>
```

---

## 🧩 Contribution Areas

| Area         | Good first issues                  | Notes                 |
| ------------ | ---------------------------------- | --------------------- |
| **Parser**   | better error spans, Unicode idents | Rust (`nom`, `serde`) |
| **Lean**     | new metrics, profunctor support    | Lean4 (`Mathlib`)     |
| **Renderer** | ε slider UI, beam animation curves | JS/TS, WebGL          |
| **Docs**     | tutorial improvements              | Markdown              |

---

## 🛡️ Ethical Reminder

Please honour the **Ethical Use Clause** in `LICENSE`.\
CatPrism is for understanding & creativity, not for harm.

Happy hacking! 🙌

