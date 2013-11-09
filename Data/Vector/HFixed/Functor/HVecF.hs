{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
module Data.Vector.HFixed.Functor.HVecF (
    HVecF(..)
  ) where

import Data.Vector.HFixed.Cont
import Data.Vector.HFixed.Class
import Data.Vector.HFixed.HVec (HVec)

-- | Partially heterogeneous vector which can hold elements of any
--   type.
newtype HVecF xs f = HVecF { getHVecF :: HVec (Wrap f xs) }

instance Arity xs => HVector (HVecF xs f) where
  type Elems (HVecF xs f) = Wrap f xs
  inspect v f = inspectF v (funToTFun f)
  construct = tfunToFun constructF
  {-# INLINE inspect   #-}
  {-# INLINE construct #-}

-- castWrapped here is used to remove constraints like:
-- `Arity (Wrap f xs)' and to replace them with `Arity xs'
instance Arity xs => HVectorF (HVecF xs) where
  type ElemsF (HVecF xs) = xs
  inspectF (HVecF v) (f :: TFun f xs a)
    = ( unInspect $ castWrapped
        (Inspect inspect :: Arity (Wrap f xs) => Inspect a f xs)
      ) v (tfunToFun f)
  constructF
    = funToTFun $ unWrapFun $ castWrapped
    ( WrapFun $ fmap HVecF construct :: Arity (Wrap f xs) => WrapFun (HVecF xs f) f xs)
  {-# INLINE inspectF   #-}
  {-# INLINE constructF #-}

newtype WrapFun r f xs = WrapFun { unWrapFun :: Fun (Wrap f xs) r }
newtype Inspect a f xs = Inspect { unInspect :: HVec (Wrap f xs) -> Fun (Wrap f xs) a -> a }
