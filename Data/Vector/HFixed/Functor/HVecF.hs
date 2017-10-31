{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE InstanceSigs         #-}
-- |
module Data.Vector.HFixed.Functor.HVecF (
    HVecF(..)
  ) where

import Control.DeepSeq
import Data.Vector.HFixed.Cont
import Data.Vector.HFixed.Class
import Data.Vector.HFixed.HVec (HVec)
import qualified Data.Vector.HFixed as H

-- | Partially heterogeneous vector which can hold elements of any
--   type.
newtype HVecF xs f = HVecF { getHVecF :: HVec (Wrap f xs) }

instance Arity xs => HVectorF (HVecF xs) where
  type ElemsF (HVecF xs) = xs
  inspectF   = undefined
  constructF = undefined
  -- inspectF (HVecF v) (f :: TFun f xs a) =
  --   case witWrapped :: WitWrapped f xs of
  --     WitWrapped -> inspect v (tfunToFun f)
  -- {-# INLINE inspectF   #-}
  -- constructF :: forall f. TFun f (ElemsF (HVecF xs)) (HVecF xs f)
  -- constructF =
  --   case witWrapped :: WitWrapped f xs of
  --     WitWrapped -> funToTFun $ fmap HVecF construct
  -- {-# INLINE constructF #-}

-- instance (Arity xs, ArityC Eq (Wrap f xs)) => Eq (HVecF xs f) where
--   (==) = H.eq
--   {-# INLINE (==) #-}

-- instance (Arity xs, ArityC Eq (Wrap f xs), ArityC Ord (Wrap f xs)) => Ord (HVecF xs f) where
--   compare = H.compare
--   {-# INLINE compare #-}

-- instance (Arity xs, ArityC NFData (Wrap f xs)) => NFData (HVecF xs f) where
--   rnf = H.rnf
--   {-# INLINE rnf #-}
