# 🌐 CatPrism 시각화 엔진 구현 가이드 (docs/VisualizationEngine.md)

이 문서는 CatPrism 구조를 Codex 등 코드 생성 모델에 전달하여  
Web 기반 시각화 도구를 자동 생성하는 데 필요한 전체 명세를 담고 있습니다.

---

## 🎯 목적

- CatPrism `.ast.json` 파일을 기반으로
- 범주 내 객체, 사상, 펑터 매핑을 시각적으로 렌더링
- 브라우저 기반 SVG, Canvas 또는 WebGL 구조 구성

---

## 📥 입력 구조 (예: Projection1.ast.json)

```json
{
  "categories": [
    {
      "name": "CategoryA",
      "objects": ["Vec2", "Mat2"],
      "morphisms": [
        { "name": "scale", "from": "Vec2", "to": "Vec2" },
        ...
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
    "epsilon": 0.15
  }
}
```

---

## 📊 시각화 목표

| 요소 | 표현 방식 |
|------|------------|
| `object` | 노드 (원형, 이름 라벨 포함) |
| `morphism` | 방향 화살표 (from → to) |
| `functor.object_map` | 범주 간 빔 연결선 |
| `functor.morphism_map` | 두 범주 간 사상 빔 |
| `epsilon` | 오차 수치 표시 (투명도 또는 색상) |
| `metric.name` | 상단 또는 툴팁에 텍스트로 표시 |

---

## 🛠️ Codex 프롬프트 예시

```
Given: a JSON file defining categories and functor mappings

Task:
Render a directed graph in browser using D3.js or plain SVG
- Draw all objects as nodes
- Morphisms as arrows
- Functor mappings as dotted beams across categories
- Display epsilon and metric

Use `examples/Projection1.ast.json` as initial test input.
```

---

## 🧠 기술 조건

- HTML/JS 기반 (one-file demo)
- `renderer/visualize.js` 또는 `.mjs` 형태
- Optional: Python HTTP server (`python -m http.server 9000`)
- CSS는 구조적 강조용 (범주 색상, functor 라벨 등)

---

## 📦 디렉토리 구조 제안

```
renderer/
├── visualize.mjs       # JS 모듈 기반 시각화 엔진
├── demo.html           # 웹 실행 진입점
├── styles.css          # 라벨/노드 시각 강조
└── README.md           # 실행 설명
```

---

CatPrism의 구조 시각화는 단순 렌더링을 넘어서  
**범주론적 해석을 직관적으로 보여주는 인터페이스**로 사용될 수 있으며,  
Codex는 이 구조를 가장 직접적으로 구현해낼 수 있는 엔진이다.
