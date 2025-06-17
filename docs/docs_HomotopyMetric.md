# 🔁 CatPrism Homotopy Metric 구조 문서 (docs/HomotopyMetric)

이 문서는 CatPrism에서 위상적 사상 비교를 위한  
**Homotopy 기반 거리(metric)** 개념을 도입하는 제안 문서입니다.

---

## 🎯 목적

- 위상적 연속성 기반의 사상 유사도 측정
- PhaseDist, LengthDist보다 구조적인 의미 차이 추적
- Homotopy class에 따른 펑터 비교 이론 기초 마련

---

## 🧠 기본 개념

### Homotopy란?

- 두 사상 \( f, g : X \to Y \) 사이에 연속 변형 \( H : X × [0,1] \to Y \)가 존재하면
- \( f \simeq g \) (homotopic)

---

## 📏 Homotopy Metric 정의 (제안형)

\[
d_{hom}(f, g) =
\begin{cases}
0 & \text{if } f \simeq g \\
α(f, g) & \text{if not homotopic (energy/cost of H)}
\end{cases}
\]

- \( α(f, g) \): 사상의 연결 경로 길이 or 연속성 붕괴 정도

---

## 🧬 DSL 적용 구조

```cat
metric HomotopyDist {
  lambda (f,g) => if homotopic(f,g) then 0 else energy(f,g)
}
```

- 추후 DSL 확장 시 `homotopic(f,g)`와 `energy(f,g)` 함수 정의 필요

---

## 📐 Lean 증명 고려사항

- Homotopy relation: `continuous_map` & `homotopy_with`
- `Mathlib4.Topology.Homotopy` 필요
- 증명 대상: `F.map(g ∘ f) ≃ F.map(g) ∘ F.map(f)`

---

## 📊 사용 예시

- `Shape → Display` 예제에서 회전/스케일 사상 간 유사도 측정
- `Circle → Circle` 에서 자명한 loop vs twist 비교

---

## 📘 확장 아이디어

- Homotopy category 도입 (`π₁(C)`)
- Hom-set 대신 Homotopy class 기반 DSL 문법
- Homotopy-aware 시각화 (loop 구조, 공명 경로 강조)

---

CatPrism은 단순한 거리 기반 펑터 검증을 넘어,  
**형상, 연속성, 변형 가능성까지 포함한 위상적 사상 비교 언어**로 확장될 수 있습니다.
