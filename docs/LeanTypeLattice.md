# 🧱 CatPrism Lean 타입 격자 구조 문서 (docs/LeanTypeLattice.md)

이 문서는 CatPrism이 활용하는 Lean 증명 구조에서  
**타입 간 위계, 포함, 투영 관계를 격자(lattice)** 로 정리하고,  
이것이 DSL 해석 및 구조 증명에 미치는 영향을 분석합니다.

---

## 🧠 목적

- 구조 내 사상과 객체의 타입 체계 정리
- 합성 가능성, 펑터 투영 가능성 판단의 수학적 근거 제공
- Lean 내 타입 격자 위에서 의미 흐름 추적

---

## 📐 기본 구성

- 타입 격자 = 객체 간 포함 관계 + 사상 허용성 판정 기반
- 정점: Type (객체)
- 엣지: ⊆, ⊇, ↣ (incl, projective map)

---

## 🔢 예시

```lean
inductive Shape
| Circle
| Triangle
| Square

inductive Display : Shape → Type
| render : ∀ s : Shape, Display s
```

- `Shape ⊆ Display`
- `Circle ⊆ Shape ⊆ Display`

---

## 🔗 Functor 내에서의 적용

```lean
F : ShapeCategory ⥤ RenderSpace
F.map : Morph s₁ s₂ → Morph (F(s₁)) (F(s₂))
```

- `F.map`의 정의 가능성은 타입간 사상 허용 조건에 따라 달라짐
- 일부 `s₁ → s₂`가 type-incompatible이면 증명 실패

---

## 📊 시각화

- 타입 격자는 Hasse Diagram으로 표현 가능
- 객체 간 사상 정의는 ⊤, ⊥ 위치 또는 meet/join 연산자로 해석

---

## 🧮 격자 연산

| 연산 | 의미 |
|------|------|
| ⊓ (meet) | 공통 하위 타입 |
| ⊔ (join) | 최소 공통 상위 타입 |
| ≼ | 포함 관계 |

---

## 🔍 DSL 적용 가능성

```cat
type_lattice {
  Circle ⊆ Shape
  Shape ⊆ Renderable
}
```

- 사상 `rotate : Circle → Triangle`이 허용되는지 자동 판정 가능

---

## 📘 결론

LeanTypeLattice는 CatPrism 구조를  
단순 연결을 넘어서 **타입 계층, 의미 투영, 합성 조건의 수학적 모델로 정렬**하며,  
펑터 증명 흐름의 정밀한 해석 기반이 된다.
