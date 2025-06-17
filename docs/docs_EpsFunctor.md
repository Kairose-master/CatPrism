# 🧩 EpsFunctor 구조 정의 문서 (docs/EpsFunctor)

CatPrism의 핵심 구조 중 하나는 `EpsFunctor`이며,  
이는 사상의 합성을 **완벽하게 보존하지 않아도 되는 허용 구조 펑터**를 정의합니다.

---

## 📐 기본 개념

```lean
structure EpsFunctor
  {C D : Type u} [CatPrismCategory C] [CatPrismCategory D]
  (δ : {A B : C} → (A ⟶ B) → (A ⟶ B) → ℝ) (ε : ℝ) where
    F        : C ⥤ D
    comp_ok  : ∀ {A B C₁} (f : A ⟶ B) (g : B ⟶ C₁),
                  δ (F.map (g ≫ f)) (F.map g ≫ F.map f) ≤ ε
```

- `δ`: 두 사상 간 거리 (PhaseDist, LengthDist 등)
- `ε`: 합성 왜곡 허용 범위
- `F`: 표준 범주론 펑터
- `comp_ok`: 합성 보존 조건 (`δ(g ∘ f, g ∘' f') ≤ ε`)

---

## 🎯 CatPrism에서의 적용 흐름

1. `.cat`에서 functor 블록에 `epsilon`과 `distortion_metric` 선언
2. 파서가 이를 `EpsFunctor` 구조로 Lean에 매핑
3. `verify_comp` 전술로 자동 증명 or 수동 증명 수행
4. CI 통과 시 해당 펑터의 ε-보존성 보장

---

## ✅ 사용 예시 (Lean)

```lean
def F_proj : EpsFunctor (δ := PhaseDist) 0.15 where
  F := {
    obj := ...
    map := ...
  }
  comp_ok := by verify_comp
```

---

## 🧠 설계 철학

- 현실의 구조 변환은 항상 완벽하지 않음
- 의미론적으로 “대부분 보존”되는 구조를 정량적으로 증명하고 싶음
- `ε`는 그 허용 오차를 수학적으로 정의해주는 핵심 매개변수

---

## 🔗 관련 요소

| 구성요소 | 연동 구조 |
|----------|-----------|
| `Metric` | δ 정의 (거리 함수) |
| `epsilon` | 허용 왜곡 한계 |
| `comp_ok` | 증명 대상 필드 |
| `verify_comp` | 자동화된 증명 전술 |
| `parser.rs` | DSL → EpsFunctor 변환 처리 |
| `export.rs` | Lean 템플릿 치환기 (`functor.lean`) |

---

## 📘 요약

EpsFunctor는  
**“범주 간 의미 구조를 최대한 보존하면서도 유연하게 사상을 옮길 수 있는 펑터 구조”**이며,  
CatPrism 시스템의 **정량적 증명 기반**을 형성하는 핵심 구조체입니다.
