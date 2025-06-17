# 🧠 CatPrism Lean 기반 구조 문서 (docs/LeanFoundation)

이 문서는 CatPrism DSL이 연결되는 Lean4 기반 수학 정형화 구조를 설명합니다.  
Lean은 CatPrism의 `.cat → .lean` 변환 후 증명 가능성을 판단하는 핵심 증명 엔진입니다.

---

## 🔧 사용되는 핵심 Lean 라이브러리

| 모듈 | 설명 |
|------|------|
| `Mathlib4.CategoryTheory.Functor` | 범주 및 펑터 구조 |
| `Mathlib4.Topology.MetricSpace.Basic` | 거리 기반 위상 구조 |
| `Mathlib4.LinearAlgebra.Basic` | 벡터, 행렬, 사상 관련 정의 |
| `Init.Tactic` | `by verify_comp`, `sorry`, `simp` 등의 전술 |
| `Elan`, `Lake` | Lean 환경 및 빌드 시스템 구성

---

## 🧩 CatPrism ↔ Lean 구조 대응

| CatPrism DSL | Lean 구조 | 설명 |
|--------------|-----------|------|
| `category` | `CatPrismCategory` class | 범주 정의 |
| `object` | `Type` / `Inductive` | 객체 |
| `morphism` | `Hom a b`, `Morph` | 사상 |
| `metric` | `PhaseDist`, `LengthDist` 함수 | 위상 거리 |
| `functor` | `EpsFunctor` 구조체 | ε-보존 펑터 |

---

## 📐 EpsFunctor 구조 (요약)

```lean
structure EpsFunctor (δ : ...) (ε : ℝ) where
  F : C ⥤ D
  comp_ok : ∀ f g, δ(F(g ∘ f), F(g) ∘ F(f)) ≤ ε
```

- 증명 대상 핵심 구조
- `verify_comp` 전술 또는 수동 증명 삽입

---

## 📦 Lean 프로젝트 구조

```text
core/lean/
├── AutoGen/        # 변환된 .lean 펑터 증명
├── Core.lean       # 공통 구조 정의 (EpsFunctor, PhaseDist 등)
├── CatPrism_examples.lean # 예제별 증명 모음
├── lakefile.lean   # Lean 빌드 진입점
└── Main.lean       # 전체 증명 실행점 (선택)
```

---

## 🛠️ 빌드 방법

```bash
cd core/lean
lake build
```

- `.cat → .lean` 후 이 명령으로 증명 전체 컴파일
- `Mathlib4`가 연결되어 있어야 증명 성공

---

## 📘 확장 제안

- `HomotopyMetric` → `HomotopyWith`와 연동
- `EpsFunctor` 파생 구조: `AdjointFunctor`, `NaturalTransformation`
- Tactic 자동 생성기: `derive_metric`, `check_commute`

---

CatPrism의 Lean 통합은 단순 변환이 아니라  
**구조적 사상들이 수학적으로 증명 가능한지 실질적으로 검증하는 플랫폼**이다.
