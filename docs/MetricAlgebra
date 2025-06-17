# ➕ CatPrism Metric Algebra 문서 (docs/MetricAlgebra)

이 문서는 CatPrism DSL 및 증명 시스템 내에서  
여러 메트릭 구조를 **연산 대수적으로 결합**하거나 비교하기 위한  
기초적인 메트릭 연산 체계를 정의합니다.

---

## 📐 목적

- 여러 메트릭을 조합하여 새로운 복합 거리 정의
- ε-보존 판단을 메트릭 연산으로 일반화
- 위상, 거리, 크기 개념을 통합적인 지표로 사용

---

## 🧩 메트릭 연산 규칙

### 1. 합성 (Additive Metric)

\[
d_{sum}(f,g) = d_1(f,g) + d_2(f,g)
\]

- 예: `PhaseDist + LengthDist`  
- 의미: 위상 + 크기 왜곡 모두 고려

---

### 2. 가중 평균 (Weighted)

\[
d_{avg}(f,g) = w_1 \cdot d_1(f,g) + w_2 \cdot d_2(f,g)
\]

- \( w_1 + w_2 = 1 \)
- 예: 70% 위상, 30% 거리 중심

---

### 3. 최대 기준 (Max)

\[
d_{max}(f,g) = \max(d_1(f,g), d_2(f,g))
\]

- 의미: 가장 큰 왜곡만 기준으로 판단
- 보수적인 보존 판정

---

### 4. 조건부 메트릭

```cat
metric Combo {
  lambda (f,g) =>
    if phase(f) == phase(g)
    then abs(len(f) - len(g))
    else 999
}
```

- 설명: 위상이 같을 때만 거리 비교
- 활용: 구조적 분기 기준

---

## 🧠 Lean 확장 구상

```lean
def CombinedMetric (d₁ d₂ : δ) (w₁ w₂ : ℝ) :=
  λ f g => w₁ * d₁ f g + w₂ * d₂ f g
```

- 메트릭 인스턴스를 함수로 조합
- `verify_comp` 적용 가능

---

## 📘 DSL 적용 예시

```cat
metric PhasePlusLength {
  lambda (f,g) => phaseDist(f,g) + lenDist(f,g)
}
```

---

## 📊 요약

| 연산 | 의미 | 사용 시기 |
|------|------|------------|
| 합 | 총 왜곡량 고려 | 종합 판단 |
| 평균 | 가중 영향 조절 | 복합 구조 |
| 최대 | 가장 큰 손실 기준 | 보수적 평가 |
| 조건부 | 특정 상황만 비교 | 구조 분기 |

---

Metric Algebra는 단순 거리 비교를 넘어,  
**CatPrism 내 구조적 의미론의 수학적 계산 기초**로 작용할 수 있습니다.
