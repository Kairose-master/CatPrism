# 🔧 Haskell 인터페이스 설계 문서 (haskell/README.md)

이 문서는 CatPrism DSL 파서 및 증명 도구를  
Haskell 기반 형식 시스템과 연동하기 위한 인터페이스 설계 초안입니다.

---

## 🎯 목적

- CatPrism 구조를 Haskell 타입/함수로 표현
- `.cat` → `Functor Haskell` 변환 가능성 평가
- 타입 클래스 기반 DSL 인터프리터 구현

---

## 📐 구조 설계 개요

### Category 클래스

```haskell
class Category cat where
  id  :: cat a a
  (.) :: cat b c -> cat a b -> cat a c
```

### 객체/사상 모델링

```haskell
data Vec2 = ...
data Mat2 = ...
data Morph a b = Morph String
```

### 펑터 구조

```haskell
data FunctorMap c d = FunctorMap {
  objMap :: c -> d,
  morMap :: forall a b. Morph a b -> Morph (c a) (c b)
}
```

---

## 🔁 CatPrism 대응 구조

| DSL 구조 | Haskell 매핑 |
|----------|---------------|
| `object A` | 타입 A |
| `morphism f : A -> B` | `Morph A B` |
| `functor F {...}` | `FunctorMap C D` 값 |

---

## 🔧 추후 구현 가능 컴포넌트

- `cat-to-hs`: `.cat` → `.hs` 변환기
- Haskell용 verifier: `verifyComp :: FunctorMap -> Bool`
- Lean ↔ Haskell 증명 경로 비교기 (`.lean`, `.hs` 대응)

---

## 📦 디렉토리 구조 제안

```
haskell/
├── lib/
│   └── CatPrism/Core.hs
├── test/
│   └── Example1.hs
├── app/
│   └── Main.hs
└── README.md
```

---

Haskell 인터페이스는 CatPrism 구조의 타입/증명/구문 표현을  
**함수형 패러다임으로 변환하고 검증하는 실험 공간**이 될 수 있습니다.
