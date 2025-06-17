# 🧠 CatPrism Lean 증명 전술 문서 (docs/LeanProofTactics.md)

이 문서는 CatPrism 구조를 Lean4에서 증명할 때 사용하는  
전술(tactic)들의 설계, 구현 흐름, 자동화 방식 등을 설명합니다.

---

## 🎯 목적

- `.lean`으로 변환된 `EpsFunctor` 구조에 대해
- `comp_ok` 조건을 자동 증명 또는 수동 삽입
- `ε` 기반 증명 전략을 제공

---

## 🧩 핵심 전술 목록

| 전술 이름 | 설명 |
|-----------|------|
| `verify_comp` | δ(F(g ∘ f), F(g) ∘ F(f)) ≤ ε 자동화 |
| `derive_metric` | 사용자 정의 metric 기반 전술 생성기 |
| `comp_sorry` | 증명 실패 시 임시 삽입 (`sorry`) |
| `fail_log` | δ > ε 인 경우 로그 출력 및 리포트 |

---

## 🧾 기본 구조

```lean
structure EpsFunctor (δ : ...) (ε : ℝ) where
  F : C ⥤ D
  comp_ok : ∀ f g, δ(F(g ∘ f), F(g) ∘ F(f)) ≤ ε
```

---

## 🛠️ 전술 구현 예시

```lean
tactic verify_comp :=
  intros f g
  simp [F]
  apply metric_bound_theorem
  decide
```

- 실제 구성은 metric 종류, F.map 구성 방식에 따라 달라짐
- `simp`, `calc`, `linarith`, `rewrite` 조합 사용 가능

---

## ⚙️ 사용자 정의 metric 대응

```lean
instance : HasPhase MyCategory where
  phase := ...
```

→ `derive_metric PhaseDist` 호출 시  
`phase` 기반 자동 비교식 생성

---

## 🧠 확장 구상

| 전술 | 설명 |
|------|------|
| `collapse_detect` | δ > ε 되는 시점 로그로 리턴 |
| `local_comp_check` | 사상 쌍 단위로 컴포지션 판정 |
| `epsilon_profile` | 전체 사상에서 δ 분포 출력 |

---

## 📘 결론

CatPrism의 Lean 전술은  
**구조적 위상 보존을 자동 증명하거나 붕괴를 탐지하는 연산 흐름**으로,  
수학적으로 의미론을 추론 가능한 구조로 변환한다.
