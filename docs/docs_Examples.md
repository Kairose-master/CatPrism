# 🧪 CatPrism Examples 설명 문서 (docs/Examples)

이 문서는 CatPrism에 포함된 대표 `.cat` 예제 파일들의 구조와 목적을 설명합니다.  
각 예제는 하나의 범주론 구조와 ε‑functor 적용 사례를 포함하고 있으며,  
자동 파싱, Lean 증명, 시각화가 모두 가능하도록 설계되어 있습니다.

---

## 📂 예제 목록

### ✅ Projection1.cat
- **설명**: 벡터공간 → 디스플레이공간 투영
- **범주**: `CategoryA → CategoryB`
- **사상**: `scale`, `rotate`, `multiply`
- **메트릭**: `PhaseDist`
- **ε 값**: 0.15
- **특징**: 가장 기본적인 ε‑펑터 예제, CI/Lean/WebGL 100% 작동

---

### ✅ Example2.cat
- **설명**: `2×2` 행렬 범주 → 위상 공간 변환
- **범주**: `Mat2 → Phase`
- **사상**: `rot90`, `scale2`, `anyM`
- **메트릭**: `PhaseDist`
- **ε 값**: 0.30
- **특징**: 행렬 → 위상 추출, `phase(det M)` 활용 구조

---

### ✅ Example3.cat
- **설명**: 그룹 → 집합으로의 forgetful functor
- **범주**: `Groups → Sets`
- **메트릭**: `Δzero` (완전 보존)
- **ε 값**: 0
- **특징**: 고전적인 구조의 정확 보존 모델

---

### ✅ Example4.cat
- **설명**: 도형 구조 → 시각적 표현공간
- **범주**: `Shape → Display`
- **사상**: `rotate45`, `scale1.5`, `embed`
- **메트릭**: 두 개 (`PhaseDist`, `LengthDist`)
- **ε 값**: 0.20 / 0.50
- **특징**: 하나의 구조에 두 개의 펑터 적용, 비교 실험

---

## 🔧 변환 및 시각화 예시

```bash
# JSON 변환
catprism parse --json examples/Example2.cat

# Lean 변환
catprism export-lean --input examples/Example2.cat

# Lean 증명
cd core/lean && lake build

# Web 시각화
cd renderer && python -m http.server 9000
```

---

## 📘 정리

| 예제 | 메트릭 | ε | 설명 |
|------|--------|----|------|
| Projection1 | PhaseDist | 0.15 | 투영 구조 기본 |
| Example2    | PhaseDist | 0.30 | 행렬 → 위상 |
| Example3    | Δzero     | 0.00 | 정확 보존 |
| Example4    | PhaseDist / LengthDist | 0.20 / 0.50 | dual metric 실험 |

---

CatPrism의 예제들은 단순 테스트를 넘어서  
**범주론적 구조의 실제 해석 가능성과 정량적 증명 가능성**을 보여주는 최소단위 실험입니다.
