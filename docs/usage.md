# 📖 CatPrism Usage Guide

*The ε-tolerant Category-Theory DSL Toolchain*

---

## 0 · Prerequisites

| Tool       | Version           | Install                        |
| ---------- | ----------------- | ------------------------------ |
| **Rust**   | ≥ 1.75            | `rustup install stable`        |
| **Node**   | ≥ 18              | `nvm install 18 && nvm use 18` |
| **Lean 4** | ≥ 4.3             | `elan toolchain install 4.3.0` |
| **Lake**   | Lean 4 설치 시 자동 포함 |                                |

---

## 1 · Clone & Submodules

```bash
git clone --recursive https://github.com/your-handle/CatPrism.git
cd CatPrism
```

---

## 2 · Build the Parser (`catprism` CLI)

```bash
cd parser
cargo build --release
# → parser/target/release/catprism
```

---

## 3 · `.cat` → JSON (AST for Web)

```bash
./target/release/catprism parse --input ../examples/Projection1.cat --output ../examples/Projection1.cat.ast.json
# → examples/Projection1.cat.ast.json
```

---

## 4 · `.cat` → Lean (proof export)

```bash
./target/release/catprism export-lean --input ../examples/Projection1.cat
# → core/lean/AutoGen/Projection1.lean
```

---

## 5 · Compile Lean Proofs

```bash
cd ../../core/lean
lake build      # ε-functor proofs ✓
```

---

## 6 · Visualise in Browser

```bash
cd ../../renderer
python -m http.server 9000
# open  http://localhost:9000/demo.html
```

*Mermaid graph + WebGL ε-beam animation appears.*

---

## 7 · CI Integration

`/.github/workflows/lean-ci.yml` 자동 동작:

1. Rust parser 빌드
2. 모든 `examples/*.cat` → Lean 변환
3. `lake build` 실행해 증명 검증

파일 오류 → ❌ / 완성 → ✅

---

## 8 · Add Your Own Example

```bash
# 1. place MyFunctor.cat under examples/
catprism parse --input examples/MyFunctor.cat --output examples/MyFunctor.cat.ast.json
catprism export-lean --input examples/MyFunctor.cat
cd core/lean && lake build
```

---

## 9 · Command Quick-Reference

| 목적             | 명령                                           |
| -------------- | -------------------------------------------- |
| JSON AST       | `catprism parse --input foo.cat --output foo.cat.ast.json` |
| Lean export    | `catprism export-lean --input foo.cat`       |
| Build proofs   | `lake build` (in `core/lean`)                |
| Local web demo | `python -m http.server 9000` (in `renderer`) |

---

## 10 · FAQ

| Q                                 | A                                                            |
| --------------------------------- | ------------------------------------------------------------ |
| \`\`\*\* 파일 아이콘이 위너워서 상상치 않아요\*\* | `.cat`은 예전 Windows catalog 확장자입니다. 연결 프리그램을 VS Code로 변경해주세요. |
| \`\`\*\* Lake 에러\*\*              | `lake init`으로 프로젝트 초기화 후 `lakefile.lean`이 있는지 확인하세요.         |
| **BibTeX “key not found” 경고**     | `.bib`에 해당 key 항목을 추가하면 해결됩니다.                               |

---

## 11 · License & Ethics

CatPrism is released under the **MIT License** with an additional Ethical-Use clause:

> *Use CatPrism to build systems of understanding, not systems of harm.*

---

**Happy Functoring!** 🐱🌈

