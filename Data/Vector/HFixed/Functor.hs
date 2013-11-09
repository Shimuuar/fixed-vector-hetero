{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Data type for working with partially heterogeneous vectors where
-- all elements have same type constructor. All functions in this
-- module work with CPS-encoded 'ContVecF' and vectors need to be
-- converted explicitly using 'cvecF' and 'vectorF'.
module Data.Vector.HFixed.Functor () where

import Data.Vector.HFixed.Class
import           Data.Vector.HFixed.Cont

import Prelude hiding (sequence)

-- | Nullary constructor
mk0 :: ContVecF '[] f
mk0 = ContVecF $ \(TFun r) -> r
{-# INLINE mk0 #-}

mk1 :: f a -> ContVecF '[a] f
mk1 a1 = ContVecF $ \(TFun f) -> f a1
{-# INLINE mk1 #-}

mk2 :: f a -> f b -> ContVecF '[a,b] f
mk2 a1 a2 = ContVecF $ \(TFun f) -> f a1 a2
{-# INLINE mk2 #-}

mk3 :: f a -> f b -> f c -> ContVecF '[a,b,c] f
mk3 a1 a2 a3 = ContVecF $ \(TFun f) -> f a1 a2 a3
{-# INLINE mk3 #-}

mk4 :: f a -> f b -> f c -> f d -> ContVecF '[a,b,c,d] f
mk4 a1 a2 a3 a4 = ContVecF $ \(TFun f) -> f a1 a2 a3 a4
{-# INLINE mk4 #-}

mk5 :: f a -> f b -> f c -> f d -> f e -> ContVecF '[a,b,c,d,e] f
mk5 a1 a2 a3 a4 a5 = ContVecF $ \(TFun f) -> f a1 a2 a3 a4 a5
{-# INLINE mk5 #-}

-- | Cons element to the vector
cons :: f x -> ContVecF xs f -> ContVecF (x ': xs) f
cons x (ContVecF cont) = ContVecF $ \f -> cont $ curryTFun f x
{-# INLINE cons #-}
