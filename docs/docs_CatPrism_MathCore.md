# 📐 CatPrism 수학적 기반 정리 (docs/CatPrism_MathCore)

이 문서는 CatPrism DSL과 Lean 증명 체계를 구성하는 데 핵심이 되는  
범주론적, 위상수학적, 대수적 수학 이론들을 정리한 참조 문서입니다.

---

## 🧠 핵심 기반 이론 목록

| 영역 | 개념 | 설명 |
|------|------|------|
| Category Theory | Category, Functor | 객체와 사상의 구조적 흐름 정의 |
| Metric Space | Pseudometric | 비대칭 거리 함수로 구조 왜곡 정량화 |
| Linear Algebra | Vector Space, Matrix | 사상의 길이·위상 정의 기반 |
| Topology | Continuity, Composition | 사상의 결합성과 불연속성 이해 |
| Type Theory | Dependent Types, Universe | Lean4 기반 형식화 시스템 연동 |

---

## 🔹 범주론 요약

- **Category**: 객체와 사상의 집합 \( (Ob, Hom) \)
- **Functor**: 두 범주 사이의 구조 보존 사상 \( F : C \to D \)
- **Composition**: \( f : A \to B, g : B \to C \Rightarrow g ∘ f : A \to C \)

---

## 🔸 Pseudometric

- CatPrism에서는 **위상 거리 대신 사상 간 왜곡량**을 사용
- 정의: \( d : X × X \to \mathbb{R}_{\geq 0} \) such that:
  - \( d(x,x) = 0 \)
  - \( d(x,y) = d(y,x) \) (optional)
  - \( d(x,z) \leq d(x,y) + d(y,z) \)

---

## 🔺 ε-Functor 구조

- 완전한 합성 보존 \( F(g ∘ f) = F(g) ∘ F(f) \) 대신,
- \( d(F(g ∘ f), F(g) ∘ F(f)) \leq ε \) 를 만족하는 **근사 구조**

CatPrism은 이 구조를 Lean에서 `EpsFunctor`로 증명 가능하게 한다.

---

## 🧮 Linear 정의

- `phase(f)` = 복소평면에서 사상의 위상 (예: `arg(det(f))`)
- `len(f)` = 사상의 크기 (예: `||v||`, `tr(f*fᵀ)`)

---

## 🧾 위상적 해석

- 위상적 구조 없이도 의미론적 “거리”를 부여하는 방식으로
- Lean에서는 `MetricSpace`, `TopologicalSpace`로 확장 가능

---

## 🔗 Lean 수학 라이브러리 참조

- `Mathlib4.CategoryTheory.Functor`
- `Mathlib4.Topology.MetricSpace`
- `Mathlib4.LinearAlgebra.Basic`

---

## 🧠 요약

CatPrism은 단순한 문법 DSL이 아니라  
**수학적으로 증명 가능한 구조적 해석기**이며,  
그 기반에는 범주론 + 위상 + 대수 + Lean 형식화가 통합되어 있다.
