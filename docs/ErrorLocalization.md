# 🧭 CatPrism 오류 국소화 구조 문서 (docs/ErrorLocalization.md)

이 문서는 CatPrism DSL 또는 Lean 증명 흐름에서 발생하는  
구조적 오류(증명 실패, 의미 붕괴 등)를  
**위치 기반으로 국소화(Localization)** 하여 추적하고 해석하는 방법을 제안합니다.

---

## ❗ 오류 유형

| 유형 | 설명 |
|------|------|
| δ > ε | 보존 실패 (펑터 왜곡) |
| F(g ∘ f) undefined | 사상 누락 |
| proof `sorry` | 증명 불가능 또는 미정 |
| morphism conflict | 사상명이 중복되거나 연결 오류 |

---

## 📌 구조 기반 오류 추적

- `.cat` 구조 → AST → Graph
- `comp_ok` 실패 위치 → 사상 쌍 단위 식별
- `collapse_log` 자동 생성 가능

---

## 🧩 DSL 확장 예시

```cat
error_trace {
  at: CategoryA
  morphism_pair: [f, g]
  reason: "delta = 0.22 > epsilon = 0.15"
  suggestion: "Check PhaseDist definition"
}
```

---

## 🧠 시각화 연동

- 붕괴 지점 엣지 강조 (`color: red`, `stroke-dash`)
- 오류 사상 마우스오버 시 설명 툴팁
- functor 매핑 중단점 표시

---

## 🧪 Lean 증명 자동 감지

```lean
if δ(f, g) > ε then
  log_failure f g δ ε
  apply sorry
```

- `log_failure`는 `.json` 또는 `.md`로 저장 가능
- `lake build` 후 `.errorlog` 자동 생성 가능성

---

## 📘 정리 구조

| 단계 | 도구 | 출력 |
|------|------|------|
| parse | `parser.rs` | `.ast.json` |
| check | `verify_comp` | success / failure |
| localize | `error_logger.rs` | collapse points |
| render | `visualize.js` | 붕괴 엣지 강조 |

---

ErrorLocalization은 CatPrism의 구조적 신뢰성을 높이기 위한  
**정량적이고 위치 기반의 해석 체계**이며,  
디버깅 뿐만 아니라 구조 흐름의 왜곡 분석에도 활용될 수 있다.
