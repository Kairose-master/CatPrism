# 📦 CatPrism AST JSON Schema 문서 (docs/JSON_Schema)

이 문서는 `.cat` DSL 파일이 파싱된 후 생성되는  
중간 표현 형식인 `Projection1.ast.json` 등의 **JSON AST 구조**를 문서화한 것입니다.

---

## 📘 최상위 구조: CatPrismAST

```json
{
  "categories": [...],
  "metric": {...},
  "functor": {...}
}
```

- `categories`: 범주 목록
- `metric`: 메트릭 정의 블록
- `functor`: 펑터 및 대응 정의

---

## 🧱 categories : [Category]

```json
{
  "name": "CategoryA",
  "objects": ["Vec2", "Mat2"],
  "morphisms": [
    { "name": "scale", "from": "Vec2", "to": "Vec2" }
  ]
}
```

| 필드 | 설명 |
|------|------|
| `name` | 범주 이름 |
| `objects` | 객체 이름 배열 |
| `morphisms` | 사상 구조 목록 (`name`, `from`, `to`) 포함 |

---

## 📏 metric : Metric

```json
{
  "name": "PhaseDist",
  "lambda": "abs(phase(f) - phase(g))"
}
```

| 필드 | 설명 |
|------|------|
| `name` | 메트릭 이름 |
| `lambda` | 거리 함수 정의 (문자열로 파싱됨) |

---

## 🔁 functor : FunctorMap

```json
{
  "name": "F",
  "from": "CategoryA",
  "to": "CategoryB",
  "object_map": {
    "Vec2": "DisplayVec"
  },
  "morphism_map": {
    "scale": "scaleOut"
  },
  "epsilon": 0.15,
  "rule": "preserve_composition_within ε"
}
```

| 필드 | 설명 |
|------|------|
| `name` | 펑터 이름 |
| `from`, `to` | 시작/목표 범주 이름 |
| `object_map` | 객체 매핑 해시맵 |
| `morphism_map` | 사상 매핑 해시맵 |
| `epsilon` | 허용 오차 |
| `rule` | 증명 대상 규칙

---

## 📚 전체 스키마 흐름

```
.cat → parser.rs → CatPrismAST → serde_json → *.ast.json
```

- JSON 구조는 그대로 `Lean`, `Web`, `Mermaid`, `TikZ`로 연동 가능
- 추후 스키마 검증을 위한 공식 `.schema.json`으로 확장 예정

---

## ✅ 샘플 파일: Projection1.ast.json

```json
{
  "categories": [
    {
      "name": "CategoryA",
      "objects": ["Vec2", "Mat2"],
      "morphisms": [
        { "name": "scale", "from": "Vec2", "to": "Vec2" }
      ]
    }
  ],
  "metric": {
    "name": "PhaseDist",
    "lambda": "abs(phase(f) - phase(g))"
  },
  "functor": {
    "name": "F",
    "from": "CategoryA",
    "to": "CategoryB",
    "object_map": { "Vec2": "DisplayVec" },
    "morphism_map": { "scale": "scaleOut" },
    "epsilon": 0.15,
    "rule": "preserve_composition_within ε"
  }
}
```

---

CatPrism의 AST 구조는 단순 출력용 포맷이 아니라,  
**형식 추론 · 증명 변환 · 시각화의 허브 역할**을 수행하는 핵심 구조입니다.
