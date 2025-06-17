# 📘 CatPrism DSL 문법 명세서 (Spec_Syntax)

CatPrism은 범주론적 구조를 DSL로 정의하기 위해 만들어졌으며,
아래와 같은 고정된 키워드와 구문 규칙을 따른다.

---

## 📐 주요 문법 구조

### 1. 범주 정의
```cat
category CategoryName {
  object A
  object B

  morphism f : A -> B
  morphism g : B -> A
}
```
- `category`: 범주의 시작을 나타냄  
- `object`: 객체 선언  
- `morphism`: 사상 선언 (함수형 → 표현)

---

### 2. 메트릭 정의
```cat
metric PhaseDist {
  lambda (f,g) => abs(phase(f) - phase(g))
}
```
- `metric`: 사상 간 거리 함수 정의  
- `lambda`: 두 사상 f, g에 대한 거리 계산 식

---

### 3. 펑터 정의
```cat
functor F from CategoryA to CategoryB {
  object_map {
    A -> A1
    B -> B1
  }
  morphism_map {
    f -> f1
    g -> g1
  }

  epsilon           : 0.15
  distortion_metric : PhaseDist
  rule              : preserve_composition_within ε
}
```
- `functor`: 펑터 정의  
- `object_map`: 객체 간 매핑  
- `morphism_map`: 사상 간 매핑  
- `epsilon`: 허용 가능한 왜곡 한계  
- `distortion_metric`: 사용할 메트릭 지정  
- `rule`: 보존 조건 명시

---

## 📏 기본 메트릭 예시

| 이름         | 정의                                |
|--------------|-------------------------------------|
| `PhaseDist`  | `abs(phase(f) - phase(g))`          |
| `LengthDist` | `abs(len(f) - len(g))`              |
| `Δzero`      | `0` (항상 0, exact composition용) |

---

## 📘 참고 사항

- `.cat` 문법은 줄 단위 파서로 동작하며, 순서에 민감하지 않음  
- 모든 사상은 `from -> to` 형식으로 명시되어야 함  
- 각 구조는 `{}` 블록 내부에 정의되어야 함

---

CatPrism DSL은 구조적 의미론에 근거한 언어이며,  
엄격한 문법 명세를 통해 자동 변환, Lean 증명, 시각화를 보장한다.
