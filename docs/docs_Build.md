# 🛠️ CatPrism Build & CI 문서 (docs/Build)

이 문서는 CatPrism 시스템의 전체 빌드 흐름,  
명령어 단계, GitHub Actions 연동 구조를 문서화합니다.

---

## 🧱 전체 빌드 구조

```text
.cat ──▶ parse.rs ──▶ ast.rs ──▶ export.rs ──▶ .lean ──▶ lake build
             │                             │
             └──────▶ JSON AST (.ast.json) └──▶ CI + Lean proof
```

---

## 📦 로컬 빌드 절차

### 1. Rust 파서 빌드
```bash
cd parser
cargo build --release
```

### 2. `.cat` → JSON AST
```bash
./target/release/catprism parse --input examples/Projection1.cat --output examples/Projection1.cat.ast.json
```

### 3. `.cat` → Lean 변환
```bash
./target/release/catprism export-lean --input examples/Projection1.cat
```

### 4. Lean 증명 빌드
```bash
cd core/lean
lake build
```

---

## ✅ GitHub Actions 연동

파일: `.github/workflows/lean-ci.yml`

### 트리거 조건

```yaml
on:
  push:
    paths:
      - 'examples/**/*.cat'
      - 'parser/**'
      - 'core/lean/**'
```

### 주요 단계

| 단계 | 설명 |
|------|------|
| Checkout | Git 서브모듈 포함 전체 클론 |
| Rust Setup | `cargo build`로 파서 빌드 |
| Parse & Export | `.cat` → `.lean` 자동 변환 |
| Lean Setup | `elan`, `lake build` 설치 및 실행 |
| Build Test | 증명 성공 여부 확인 (Green ✅ / Fail ❌) |

---

## 🧪 CI 상태 확인

GitHub PR이나 Push 시  
- `.cat` 변경 → 자동 Lean 변환 + build  
- 실패 시 머지 불가  
- 성공 시 badge 표시: `Lean Proofs Passed ✅`

---

## 📘 참고

- `lakefile.lean`은 `core/lean` 내부에 있어야 함
- 모든 `.lean`은 `AutoGen/` 디렉토리에 생성됨
- `lake build`는 `mathlib4`와 연동되어야 정상 작동함

---

CatPrism은 코드와 증명을 하나의 연속된 구조로 통합하고 있으며,  
**CI를 통해 의미 구조 자체의 정합성까지 자동 검증**할 수 있습니다.
