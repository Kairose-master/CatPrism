# 🌀 CatPrism Phase 의미론 문서 (docs/PhaseSemantics)

이 문서는 CatPrism DSL 내의 `phase(f)` 개념이 갖는 의미론적 해석,  
적용 예시, 그리고 수학적 기반을 정리한 문서입니다.

---

## 🌗 Phase란 무엇인가?

- 사상 f의 위상은 \( \theta = \text{arg}(f) \)로 해석된다
- 일반적으로 복소수, 행렬, 또는 벡터의 회전 상태를 나타내며
- CatPrism에서는 의미 공간 내의 **방향성 정보**로 해석됨

---

## 📐 수학적 정의 (기본형)

- 복소수 \( z = re^{i\theta} \Rightarrow \theta = \arg(z) \)
- 행렬 M의 위상 \( \theta = \arg(\det(M)) \)
- 벡터 v의 위상 \( \theta = \arctan(\frac{v_y}{v_x}) \)

---

## 🔁 위상 기반 메트릭

CatPrism에서 가장 자주 쓰이는 메트릭:

```cat
metric PhaseDist {
  lambda (f,g) => abs(phase(f) - phase(g))
}
```

- 위상 차이를 거리로 간주하여 ε-보존 여부 판정
- 합성이 보존될수록 위상 차이는 작아짐

---

## 🔭 의미론적 해석

| 구조 | 위상 의미 |
|------|------------|
| `rotate : A → A` | 자명하지 않은 방향성 보존 |
| `scale : A → A` | 위상이 0인 위상고정 사상 |
| `multiply : M → V` | `det(M)` 기반 방향성 투영 |

---

## 💡 응용 가능성

- **의미 흐름 분석**: 텍스트 의미 이동을 위상 차로 추적
- **비유사성 측정**: 사상 간 의미 왜곡을 위상으로 표현
- **연결성 파악**: 위상 차가 작으면 의미망 내 연결이 강함

---

## 📘 Lean에서의 구현

```lean
class HasPhase where
  phase : {A B : C} → (A ⟶ B) → ℝ
  phase_arg : ∀ f, abs (phase f) ≤ π
```

- 증명 기반 위상 분석 가능
- `PhaseDist`는 `HasPhase` 인스턴스를 전제로 작동

---

## 🧠 요약

`phase(f)`는 단순 회전이 아니라,  
**사상의 의미적 방향성과 구조 보존성을 정량화하는 해석적 지표**이며,  
CatPrism의 증명 가능 구조와 시각적 메트릭 해석을 연결해주는 핵심 요소이다.
