# 🧮 CatPrism Graph Compiler 문서 (docs/GraphCompiler.md)

이 문서는 CatPrism DSL 구조를 기반으로  
**범주론적 그래프를 내부 AST로 컴파일**하고,  
그로부터 Lean, SVG, Web 시각화 등으로 변환하는 전체 파이프라인을 설명합니다.

---

## 🎯 목적

- `.cat` → `.ast.json` → 내부 그래프 객체 모델로 파싱
- 모든 객체, 사상, 펑터 정보를 그래프 노드/엣지로 표현
- 구조적 변환 가능성을 수학적으로 추론하고 구현

---

## 📂 입력 구조 예시

```cat
category CategoryA {
  object A
  object B
  morphism f : A -> B
}
```

→ 파서 → `CatPrismAST` → 내부 그래프

---

## 🧩 내부 그래프 모델

```haskell
data Graph = Graph {
  nodes :: [Node],
  edges :: [Edge],
  functors :: [FunctorEdge]
}

data Node = Node {
  id   :: String,
  role :: "object" | "category"
}

data Edge = Edge {
  source :: String,
  target :: String,
  label  :: String
}

data FunctorEdge = FunctorEdge {
  fromObj :: String,
  toObj   :: String,
  via     :: String,     -- functor name
  epsilon :: Double
}
```

---

## 🔃 컴파일 흐름 요약

```text
.cat
 └── parser.rs
       └── ast.rs (CatPrismAST)
              └── GraphBuilder.rs
                      └── Graph{ nodes, edges, functorBeams }
```

---

## 🔎 사용 목적

- Lean 증명용 Graph → `.lean` 구조 자동 생성
- Mermaid/TikZ/SVG 시각화 출력
- 의미 해석 기반 구조 유효성 검사
- functor composition 자동 도출

---

## 🛠️ 활용 API 구상 (Rust)

```rust
fn compile_cat_to_graph(ast: CatPrismAST) -> Graph
fn render_graph_svg(g: Graph) -> String
fn export_graph_lean(g: Graph) -> String
```

---

## 📘 응용 가능성

| 출력 형태 | 사용 목적 |
|-----------|-----------|
| `.lean` | EpsFunctor 증명 코드 |
| `.svg`  | 시각화 툴 |
| `.dot`  | Graphviz 연동 |
| `.mmd`  | Mermaid 구조 분석 |
| `.tikz` | 논문용 LaTeX 출력 |

---

CatPrism의 GraphCompiler는  
**범주론을 구조적 데이터 흐름으로 환원하는 해석 장치**이며,  
구조 ↔ 증명 ↔ 시각화의 핵심 허브 역할을 수행한다.
