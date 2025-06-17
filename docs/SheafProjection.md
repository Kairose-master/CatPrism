# 🧵 CatPrism Sheaf Projection 구조 문서 (docs/SheafProjection.md)

이 문서는 CatPrism DSL의 구조적 해석을  
**층 이론(Sheaf Theory)** 기반으로 확장하여  
지역적 구조의 연속성과 전역 투영 가능성을 다루는 모델을 제안합니다.

---

## 🧠 Sheaf란?

- 공간의 열린 집합마다 데이터를 할당하고
- 제한(restriction)과 glueing 조건을 만족하는 구조

즉, 지역적 정보가 전역적 구조를 구성할 수 있을 때 Sheaf라고 함.

---

## 🔁 CatPrism과의 연결

| CatPrism 요소 | Sheaf 해석 |
|---------------|-------------|
| `object` | 열린 집합 (U) |
| `morphism` | 제한 사상 (res) |
| `functor` | 전역 구조로의 투영 |
| `epsilon` | glueing 조건의 불완전성 허용치 |

---

## 🧬 DSL 확장 예시

```cat
sheaf CategoryA {
  cover {
    U1, U2, U3
  }
  glueing_rule {
    (U1 ∩ U2) → consistency(f1, f2) < ε
  }
}
```

- 각 열린 부분 범주에서의 사상 집합
- ε 기반 접합 불일치 허용

---

## 📐 수학적 조건

- 모든 \( f_i : F(U_i) \to X \) 이 주어졌을 때,
- \( \exists! f : F(U) \to X \) such that \( f|_{U_i} = f_i \)
- CatPrism에서는 \( δ(f_i, f_j) ≤ ε \) 로 완화된 glueing 조건 사용

---

## 🔭 시각적 모델

- 각 `object` = local patch (Uᵢ)
- `morphism` = patch 간 restriction map
- 전체 `functor` = glueing 결과 전역 사상

---

## 📘 Lean 연동 구상

```lean
structure Sheaf (F : Opens X ⥤ Type) :=
  (is_sheaf : ∀ (cover : Cover X), satisfies_glueing F cover ε)
```

---

## ✨ 응용

| 영역 | 응용 가능성 |
|------|--------------|
| 시각화 | 국소 연결망으로부터 전역 구조 애니메이션 |
| 증명 | 파편화된 사상 glueing 가능 여부 판정 |
| 의미론 | 기억/의도/맥락 정보의 지역-전역 구성 해석 |

---

CatPrism의 SheafProjection 개념은  
**로컬한 의미 구조가 어떻게 전체 의미망으로 연결되는지를  
수학적으로 정식화하는 시도이며, 의미망 해석의 핵심 메타구조**가 될 수 있다.
