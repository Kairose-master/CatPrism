# 🧮 CatPrism Tensor Collapse 구조 문서 (docs/TensorCollapse.md)

이 문서는 CatPrism 내에서 **텐서곱(tensor product)** 구조를  
사상 합성의 고차 형태로 해석하고,  
그 붕괴 조건과 의미론적 파열을 수학적으로 기술합니다.

---

## 🔗 기본 개념

- 텐서곱 \( f ⊗ g \) 은 두 사상의 동시 작용 또는 병합 작용
- 범주 C × D 에서 사상 f : A → A', g : B → B' 를  
  하나의 사상 (f ⊗ g) : (A,B) → (A',B') 로 표현
- CatPrism에서는 이 구조가 Lean 또는 DSL에서 단일 사상처럼 취급됨

---

## 💥 붕괴 조건

| 상황 | 해석 |
|------|------|
| \( δ(f ⊗ g, h) > ε \) | 텐서 합성이 단일 사상 h로 투영되지 않음 |
| \( phase(f ⊗ g) ≠ phase(h) \) | 위상 왜곡 |
| \( F(f ⊗ g) = ∅ \) | 펑터가 병합 사상을 정의하지 않음 |

---

## 📘 DSL 예시

```cat
functor T from A×B to C {
  object_map {
    (A1,B1) -> C1
  }
  morphism_map {
    (f⊗g) -> h
  }
  epsilon: 0.2
  distortion_metric: PhaseDist
  rule: preserve_composition_within ε
}
```

---

## 🧬 위상적 해석

- \( f ⊗ g \) 은 두 공간에서의 위상 흐름 결합
- 결합 후 \( h \) 가 동일 위상 범주에 있지 않으면 위상 붕괴
- 붕괴시엔 사상 간 위상 합성 불일치가 발생

---

## 🔢 Lean 확장 예시

```lean
def TensorCollapse :=
  ∃ f g h, (δ (F.map (f ⊗ g), F.map h) > ε)
```

- 또는 증명 전술 내에서 `collapse_tensor_detect f g h` 정의 가능

---

## 🔭 시각화 적용

- 병합 사상 = 두 개의 빔이 한 방향으로 수렴
- 붕괴 시: 두 개의 병합선이 서로 다른 대상에 닿음 (이중 붕괴선)
- `⊗` 노드를 통해 의미 충돌 표현

---

## 🧠 의미론적 확장

| 개념 | 해석 |
|------|------|
| 텐서 사상 | 동시 작용, 다중 원인 |
| 붕괴 | 병합 실패 → 의미 분기 |
| ε-합성 불가 | 의미 구조의 병렬화 한계 도달 지점 |

---

TensorCollapse는 **복합 의미 구조의 붕괴 패턴**을  
정량적, 위상적, 증명 기반으로 기술할 수 있는  
CatPrism의 핵심 확장 개념 중 하나다.
