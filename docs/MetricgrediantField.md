# 🧮 CatPrism Metric Gradient Field 문서 (docs/MetricGradientField.md)

이 문서는 CatPrism 내에서 정의된 메트릭 함수 δ(f, g)가  
공간 위에서 **기울기 벡터장(Gradient Field)** 을 형성할 수 있다는 관점으로  
구조 붕괴, 왜곡, 의미 흐름의 방향성을 미분기하학적으로 해석하는 이론을 제안합니다.

---

## 🎯 목적

- ε-붕괴 경계면을 기하학적으로 시각화
- 사상 공간에 대한 거리 함수의 경사도 분석
- 붕괴 영역, 완만한 흐름, 위상 왜곡점 등을 정량적으로 파악

---

## 📐 기본 정의

- 각 사상 쌍 (f, g)에 대해 δ(f, g)를 정의할 때,  
  f 또는 g가 연속적으로 변할 경우 δ는 곡면 위의 함수가 됨

- 따라서 \( \nabla_f \delta(f, g) \), \( \nabla_g \delta(f, g) \)를 정의 가능

---

## 🌀 기하학적 해석

| 값 | 의미 |
|----|------|
| ∇δ ≈ 0 | 보존 안정 상태 (locally flat) |
| ∇δ ↑ | 빠르게 왜곡되는 경로 |
| ∇δ ↗↗ | 붕괴 경계면 또는 구조 임계선 |

---

## 🧾 DSL 상 표현 예시

```cat
gradient_field PhaseDist {
  from: f
  direction: g
  result: ∇f δ(f,g)
}
```

또는 시각화 로그에서:

```json
{
  "morphism_pair": ["f", "g"],
  "delta": 0.19,
  "gradient": 0.05
}
```

---

## 📊 시각화 응용

- 색상 구배: δ 크기
- 등고선: 동일 δ 선
- 벡터필드: ∇δ(f,g) 방향성 표시

---

## 🧠 Lean 확장 구상

```lean
def grad_delta (δ : Morph A B → Morph A B → ℝ) :=
  ∇ (λ f, δ(f, g))
```

- Lean에서는 수치 미분 불가능하므로 기호적 추론 + 표본 기반 근사 필요

---

## 📘 결론

MetricGradientField는 단순 거리 비교를 넘어,  
**사상 공간 위의 연속적 왜곡 흐름을 해석하고 붕괴를 예측하는 기하적 수단**이다.
