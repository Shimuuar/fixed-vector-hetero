{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE InstanceSigs         #-}
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

instance (Arity (Wrap f xs), Arity xs) => HVector (HVecF xs f) where
  type Elems (HVecF xs f) = Wrap f xs
  inspect v f = inspectF v (funToTFun f)
  construct   = tfunToFun constructF
  {-# INLINE inspect   #-}
  {-# INLINE construct #-}

instance Arity xs => HVectorF (HVecF xs) where
  type ElemsF (HVecF xs) = xs
  inspectF (HVecF v) (f :: TFun f xs a) =
    case witWrapped :: WitWrapped f xs of
      WitWrapped -> inspect v (tfunToFun f)
  {-# INLINE inspectF   #-}
  constructF :: forall f. TFun f (ElemsF (HVecF xs)) (HVecF xs f)
  constructF =
    case witWrapped :: WitWrapped f xs of
      WitWrapped -> funToTFun $ fmap HVecF construct
  {-# INLINE constructF #-}
