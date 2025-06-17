# 🪞 CatPrism Adjoint Displacement 구조 문서 (docs/AdjointDisplacement.md)

이 문서는 CatPrism에서 범주론의 핵심 구조인 **Adjoint Functor (수반 펑터)** 개념을  
**의미 공간 내 위치 이동(displacement)**으로 해석하는 관점과  
그 증명 가능성, DSL 적용 모델을 제안합니다.

---

## 🔁 기본 개념: 수반 펑터 (Adjunction)

- 펑터 F : C → D, G : D → C 가 있을 때
- \( \text{Hom}_D(F(X), Y) ≅ \text{Hom}_C(X, G(Y)) \)
- F와 G는 서로 의미론적 전후관계 (left/right context translator)

---

## 📐 CatPrism 해석

| 개념 | 해석 |
|------|------|
| F | 구조를 바깥으로 투영 (해석자) |
| G | 바깥 구조를 내부로 되돌림 (구성자) |
| displacement | F ∘ G ≠ Id or G ∘ F ≠ Id 인 경우 구조 흔들림 발생 |
| ε | 수반성이 깨지는 허용 한계 |

---

## 🧪 DSL 표현 예시

```cat
adjunction F ⊣ G {
  from: C
  to: D
  epsilon: 0.05
  rule: preserve_adjointness_within ε
}
```

또는 증명 로그:

```json
{
  "adjoint_pair": ["F", "G"],
  "direction": "C → D",
  "hom_equiv_error": 0.02
}
```

---

## 📊 시각화 적용

- F ⊣ G 구조를 양방향 빔 또는 곡선으로 표현
- ε 초과시 "displacement" 진폭/파형으로 표시
- 수반 붕괴 = 내부 ↔ 외부 흐름 불일치로 표시

---

## 🧠 Lean 증명 구성

```lean
structure AdjointEps (F G : ...) :=
  (hom_equiv : ∀ X Y, |Hom(F(X), Y) - Hom(X, G(Y))| ≤ ε)
```

- `ε = 0`인 경우는 정수반, `ε > 0`은 근사 수반 구조

---

## 📘 활용 가능성

| 영역 | 응용 |
|------|------|
| 의미 번역 | 내부 ↔ 외부 언어 간 번역 구조 해석 |
| 기억/표현 | 구성 ↔ 해석의 틀 차이 분석 |
| DSL 이론 | 수반 붕괴 시 의미 구조 단절 검출

---

AdjointDisplacement는  
**펑터쌍이 구성하는 쌍방향 의미 지도의 붕괴와  
그 위상적 불일치를 추적하는 수학적/해석적 확장 구조**다.
