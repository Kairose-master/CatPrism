# 🔀 CatPrism Functor 사례 문서 (docs/FunctorExamples)

이 문서는 다양한 종류의 펑터(Functor)를  
CatPrism DSL로 어떻게 표현할 수 있는지에 대한 예제 모음입니다.

---

## ✅ 1. Identity Functor (항등 펑터)

```cat
functor Id from CategoryA to CategoryA {
  object_map {
    A -> A
    B -> B
  }
  morphism_map {
    f -> f
    g -> g
  }
  epsilon: 0
  distortion_metric: Δzero
  rule: preserve_composition_within ε
}
```

- 설명: 구조를 전혀 변경하지 않는 자명한 펑터
- 증명: 항상 `δ(f, f) = 0` → 완전 보존

---

## 🔁 2. Forgetful Functor (그룹 → 집합)

```cat
functor U from Groups to Sets {
  object_map {
    G -> UG
    H -> UH
  }
  morphism_map {
    f -> f_set
  }
  epsilon: 0
  distortion_metric: Δzero
  rule: preserve_composition_within ε
}
```

- 설명: 군 구조를 잊고 underlying set만 유지
- 목적: 정수론, 위상군 해석에 활용

---

## ⚙️ 3. Rotation Projection Functor

```cat
functor RotProj from Mat2 to Display {
  object_map {
    M -> DM
  }
  morphism_map {
    rotate90 -> showQuarter
  }
  epsilon: 0.3
  distortion_metric: PhaseDist
  rule: preserve_composition_within ε
}
```

- 설명: 회전 사상을 시각적 표현으로 투영
- ε 값은 허용 회전 위상 차이

---

## 🔮 4. Approximate Tensor Functor

- 개념: 두 구조의 텐서곱을 하나의 사상으로 투영

```cat
functor T from A×B to C {
  object_map {
    (A1,B1) -> C1
  }
  morphism_map {
    (f⊗g) -> h
  }
  epsilon: 0.4
  distortion_metric: LengthDist
  rule: preserve_composition_within ε
}
```

---

## 📘 요약

| 이름 | 구조 | ε | 메트릭 | 설명 |
|------|------|----|--------|------|
| Id | A → A | 0 | Δzero | 자명한 펑터 |
| U | Groups → Sets | 0 | Δzero | 구조 제거 |
| RotProj | Mat2 → Display | 0.3 | PhaseDist | 위상 투영 |
| T | A×B → C | 0.4 | LengthDist | 구조 병합 |

CatPrism의 펑터 표현은 정형화된 DSL을 통해  
범주 간 의미 구조를 정량적으로 해석하고,  
자동 증명 가능한 수준까지 구조화할 수 있다.
