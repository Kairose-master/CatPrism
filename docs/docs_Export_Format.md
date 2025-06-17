# 📤 CatPrism Export Format 문서 (docs/Export_Format)

이 문서는 `.cat` DSL 파일을 Lean 코드로 변환할 때 사용하는 출력 형식(Export Format)에 대해 설명합니다.  
모든 변환은 `parser/templates/functor.lean` 템플릿을 기반으로 하며,  
AST → Lean 구조 치환 방식으로 구현됩니다.

---

## 📄 기본 템플릿 구조

```lean
def F_example : EpsFunctor (δ := PhaseDist) 0.15 where
  F := {
    obj := fun X => match X with
      | CategoryA.Vec2 => CategoryB.DisplayVec
      | CategoryA.Mat2 => CategoryB.RenderMat,
    map := fun f => match f with
      | CategoryA.scale => CategoryB.scaleOut
      | CategoryA.rotate => CategoryB.rotateOut
      | CategoryA.multiply => CategoryB.projectOut
  }
  comp_ok := by verify_comp
```

---

## 🧩 템플릿 치환 항목

| Placeholder | 설명 |
|-------------|------|
| `{source_file}` | `.cat` 원본 파일 이름 |
| `{functor_name}` | 생성된 펑터 이름 (`F_proj`, `Ftheta`) |
| `{metric}` | 메트릭 이름 (`PhaseDist`, `LengthDist` 등) |
| `{epsilon}` | 허용 왜곡 값 |
| `{object_map}` | 객체 매핑 `match` 블록 |
| `{morphism_map}` | 사상 매핑 `match` 블록 |
| `{proof_block}` | `verify_comp` or `sorry` |

---

## 🛠️ 파일 경로

- 템플릿: `parser/templates/functor.lean`
- 출력 위치: `core/lean/AutoGen/*.lean`
- 함수명 규칙: `F_<functor name lowercase>`

---

## 🧠 증명 전술 자동화

- `"preserve_composition_within ε"` → `verify_comp` 자동 삽입
- 다른 규칙 지정 시 `sorry` 사용
- 추후 사용자 정의 전술 (`tactic derive_metric`) 도입 예정

---

## 🧪 예제 대응

| 예제 | Lean 출력 파일 | 증명 상태 |
|------|----------------|-----------|
| `Projection1.cat` | `F_proj.lean` | ✅ 자동 증명 |
| `Example2.cat`    | `F_mat_phase.lean` | ✅ |
| `Example3.cat`    | `ForgetGroups.lean` | ✅ |
| `Example4.cat`    | `F_shape_phase.lean`, `F_shape_len.lean` | ✅ |

---

## 📘 요약

CatPrism의 Lean export는 단순 문자열 변환이 아니라  
**구조 정합성과 증명 목적에 기반한 형식화된 추론 코드 생성 과정**입니다.  
모든 `.cat`은 곧바로 `.lean`으로 변환되어 **증명 가능한 구조 모델**로 사용될 수 있습니다.
