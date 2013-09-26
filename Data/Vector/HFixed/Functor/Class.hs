{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE InstanceSigs          #-}
module Data.Vector.HFixed.Functor.Class (
    -- * Types
    TFun(..)
  , castFun
  , castTFun
  ) where

import Control.Applicative (Applicative(..))
import Data.Vector.HFixed.Class

-- | Newtype wrapper for function where all type parameters have same
--   type constructor
newtype TFun f as b = TFun { unTFun :: Fn (Wrap f as) b }


castFun  :: Fun (Wrap f xs) b -> TFun f xs b
castFun = TFun . unFun
{-# INLINE castFun #-}

castTFun :: TFun f xs b -> Fun (Wrap f xs) b
castTFun = Fun . unTFun
{-# INLINE castTFun #-}


----------------------------------------------------------------
-- Instances
----------------------------------------------------------------

instance (Arity xs) => Functor (TFun f xs) where
  fmap (f :: a -> b) (TFun g0 :: TFun f xs a)
    = TFun $ accumTy (\(T_fmap g) a -> T_fmap (g a))
                     (\(T_fmap r)   -> f r)
                     (T_fmap g0 :: T_fmap f a xs)
  {-# INLINE fmap #-}

newtype T_fmap f a   xs = T_fmap (Fn (Wrap f xs) a)
data    T_pure f     xs = T_pure
data    T_ap   f a b xs = T_ap (Fn (Wrap f xs) a) (Fn (Wrap f xs) b)
