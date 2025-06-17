# 🔄 CatPrism 의미 흐름 구조 문서 (docs/SemanticFlowMap.md)

이 문서는 CatPrism DSL 및 증명 구조 내에서  
**사상의 의미 흐름(Semantic Flow)** 을 추적, 정량화, 시각화하기 위한 모델을 정의합니다.

---

## 🧠 개념 정의

- `morphism`: 의미의 전달 또는 전이
- `functor`: 의미 해석의 시공간적 재배열
- `semantic flow`: 구조적 사상들이 연결되어  
  의미가 어느 방향으로 흘러가는지를 정량적으로 추적한 흐름

---

## 🧾 모델링 기본 구조

```cat
category Meaning {
  object ConceptA
  object ConceptB

  morphism evokes : ConceptA -> ConceptB
  morphism distorts : ConceptB -> ConceptA
}
```

- 의미 노드와 사상은 정보 흐름의 기호적 구조
- 방향성은 해석 과정의 한계를 드러냄

---

## 📊 시각화 구성

| 요소 | 표현 |
|------|------|
| 객체 | 의미 노드 (원형 + 라벨) |
| 사상 | 의미 흐름 (화살표, 위상색상) |
| 강도 | 위상 또는 색 농도 |
| 왜곡 | 위상 방향 차이 또는 반사 (역방향 화살표) |

---

## 🧮 의미 메트릭 확장

```cat
metric MeaningDrift {
  lambda (f,g) => semantic_distance(f, g)
}
```

- `semantic_distance`: 의미 차이 정량화 함수
- AI embedding 기반 적용 가능

---

## 🔁 Functor 해석

- 의미 흐름이 해석 공간으로 투영될 때
- 흐름 방향, 위상, 강도 모두 변환 가능
- ε 값은 의미 왜곡 허용 임계점

---

## 🧠 응용 가능성

| 영역 | 응용 |
|------|------|
| 감정 해석 | 의미 흐름이 감정 구조를 어떻게 통과하는지 추적 |
| AI 답변 구조 | 답변 내부의 의미 전이 분석 |
| 기억 구조화 | 의미 흐름의 누적 구조 = 기억 |

---

## 📘 요약

Semantic Flow Map은 CatPrism의 사상들이  
단순한 객체 연결이 아니라,  
**구조적으로 해석 가능한 의미의 흐름을 형성한다는 관점**에서  
DSL을 정량적 해석망으로 확장한다.
