# 🤖 CatPrism Codex 통합 파이프라인 문서 (docs/Codex_Pipeline)

이 문서는 CatPrism DSL과 구조 데이터를  
Codex(코드 자동 생성 모델)에 전달하여 자동 구현을 유도하는 방법과  
각 컴포넌트에 맞는 프롬프트 구조를 설명합니다.

---

## 🎯 목표

- `.cat`, `.ast.json`, `.lean`, `.hs` 파일을 기반으로
- Haskell / Lean / Rust 구조 자동 생성
- Codex가 **구조만 보고 구현하도록** 최소 명세 제공

---

## 🧱 통합 파이프라인 개요

```text
.cat → parse.rs → ast.rs
     └→ JSON (.ast.json) ─┐
                          ├─▶ Codex (prompt)
.lean (template) ─────────┘
```

---

## 📦 Codex 대상 구조 예시

| 구조 | 언어 | 목적 |
|------|------|------|
| `EpsFunctor` | Haskell | 거리 기반 펑터 구조 |
| `verifyComp` | Haskell | ε 이내 여부 검증 |
| `FunctorMap` | Haskell | object/morphism 매핑 |
| `phaseDist` | Haskell | 메트릭 함수 정의 |
| `lakefile.lean` | Lean | 증명 실행 구조 |
| `core/lean/Core.lean` | Lean | 기본 구조 정의 |

---

## 🧾 프롬프트 예시: Haskell verifier

```
Given:
  data Morph a b = Morph String
  data EpsFunctor = ...

Task:
  Implement verifyComp :: EpsFunctor -> Bool
  such that:
    For all f, g in morphism set, metric (g ∘ f, g ∘ f') ≤ ε
```

---

## 🧾 프롬프트 예시: Lean export generator

```
Given:
  JSON AST of a CatPrism functor

Task:
  Generate a Lean4 structure EpsFunctor with appropriate F.obj, F.map,
  and proof block using verify_comp tactic
```

---

## 🧠 Codex 활용 전략

- 프롬프트는 **구조를 먼저 보여주고, 구현을 유도**
- 가능한 한 타입 선언, 예제 1개 포함
- 설명은 자연어가 아닌 **유형 정보 기반**

---

## 🔧 향후 구성 계획

| 작업 | 설명 |
|------|------|
| `prompt/haskell/verify.hs` | 자동 검증기 템플릿 |
| `prompt/lean/functorGen.lean` | AST 기반 Lean 생성기 |
| `prompt/rust/parser.rs` | DSL 파서 구현기 |
| `prompt/phase/semantics.hs` | 위상 기반 해석기 |

---

Codex는 단순한 생성기가 아니라,  
CatPrism의 **구조 정보를 구체적 코드로 환원하는 증명-인터프리터**로 사용된다.
