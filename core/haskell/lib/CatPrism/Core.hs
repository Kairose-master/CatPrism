{-# LANGUAGE GADTs, RankNTypes, FlexibleInstances #-}

module CatPrism.Core where

-- | Abstract Category Class
class Category cat where
  idC  :: cat a a
  (∘)  :: cat b c -> cat a b -> cat a c

infixr 9 ∘

-- | Morphism type (named arrows)
data Morph a b where
  Morph :: String -> Morph a b

instance Show (Morph a b) where
  show (Morph name) = name

-- | Example Objects
data Vec2
data Mat2
data DisplayVec
data RenderMat

-- | Example Morphisms
scale     :: Morph Vec2 Vec2
scale     = Morph "scale"

rotate    :: Morph Vec2 Vec2
rotate    = Morph "rotate"

multiply  :: Morph Mat2 Vec2
multiply  = Morph "multiply"

-- | Functor Mapping
data FunctorMap obj1 obj2 = FunctorMap {
  objMap :: forall a. obj1 a -> obj2 a,
  morMap :: forall a b. Morph a b -> Morph (obj2 a) (obj2 b)
}

-- | Epsilon-tolerant Functor Structure
data EpsFunctor cat1 cat2 = EpsFunctor {
  fMap     :: FunctorMap cat1 cat2,
  epsilon  :: Double,
  metric   :: forall a b. Morph a b -> Morph a b -> Double
}

-- | Example metric: phase difference placeholder
phaseDist :: Morph a b -> Morph a b -> Double
phaseDist (Morph f) (Morph g) = if f == g then 0 else 0.1  -- mock

-- | Sample Functor: Projection from CategoryA to CategoryB
projectionF :: EpsFunctor Identity Identity
projectionF = EpsFunctor {
  fMap = FunctorMap {
    objMap = id,
    morMap = \m -> case m of
      Morph "scale"    -> Morph "scaleOut"
      Morph "rotate"   -> Morph "rotateOut"
      Morph "multiply" -> Morph "projectOut"
      _                -> Morph "unknown"
  },
  epsilon = 0.15,
  metric  = phaseDist
}

-- | Identity wrapper type
newtype Identity a = Identity a