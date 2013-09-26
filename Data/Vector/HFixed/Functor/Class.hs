{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
module Data.Vector.HFixed.Functor.Class (
    -- * Types
    TFun(..)
  , castFun
  , castTFun
  , HVectorF(..)
    -- * Combinators
  , curryTFun
  , uncurryTFun
  , uncurryTFun2
  , shuffleTF
  ) where

import Control.Applicative (Applicative(..))
import Data.Vector.HFixed.Class



----------------------------------------------------------------
-- Types and type classes
----------------------------------------------------------------

-- | Newtype wrapper for function where all type parameters have same
--   type constructor
newtype TFun f as b = TFun { unTFun :: Fn (Wrap f as) b }


castFun  :: Fun (Wrap f xs) b -> TFun f xs b
castFun = TFun . unFun
{-# INLINE castFun #-}

castTFun :: TFun f xs b -> Fun (Wrap f xs) b
castTFun = Fun . unTFun
{-# INLINE castTFun #-}


-- | Type class for partially homogeneous vector. Every type in the
--   vector have same type constructor.
class HVectorF v where
  -- | Elements of the vector without type constructors
  type ElemsF v :: [*]
  inspectF   :: v f -> TFun f (ElemsF v) a -> a
  constructF :: TFun f (ElemsF v) (v f)



----------------------------------------------------------------
-- Combinators
----------------------------------------------------------------

-- | Apply single parameter to function
curryTFun :: TFun f (x ': xs) r -> f x -> TFun f xs r
curryTFun (TFun f) = TFun . f
{-# INLINE curryTFun #-}

-- | Uncurry single parameter
uncurryTFun :: (f x -> TFun f xs r) -> TFun f (x ': xs) r
uncurryTFun = TFun . fmap unTFun
{-# INLINE uncurryTFun #-}

-- | Uncurry two parameters for nested TFun.
uncurryTFun2 :: (Arity xs, Arity ys)
             => (f x -> f y -> TFun f xs (TFun f ys r))
             -> TFun f (x ': xs) (TFun f (y ': ys) r)
uncurryTFun2 = uncurryTFun . fmap (fmap uncurryTFun . shuffleTF . uncurryTFun)
{-# INLINE uncurryTFun2 #-}


-- | Move first argument of function to its result. This function is
--   useful for implementation of lens.
shuffleTF :: forall f x xs r. Arity xs => TFun f (x ': xs) r -> TFun f xs (f x -> r)
{-# INLINE shuffleTF #-}
shuffleTF (TFun f0) = TFun $ accumTy
  (\(T_shuffle f) a -> T_shuffle (\x -> f x a))
  (\(T_shuffle f)   -> f)
  (T_shuffle f0 :: T_shuffle f x r xs)

data T_shuffle f x r xs = T_shuffle (Fn (Wrap f (x ': xs)) r)



----------------------------------------------------------------
-- Instances
----------------------------------------------------------------

instance (Arity xs) => Functor (TFun f xs) where
  fmap (f :: a -> b) (TFun g0 :: TFun f xs a)
    = TFun $ accumTy (\(T_fmap g) a -> T_fmap (g a))
                     (\(T_fmap r)   -> f r)
                     (T_fmap g0 :: T_fmap f a xs)
  {-# INLINE fmap #-}

instance (Arity xs) => Applicative (TFun f xs) where
  pure r = TFun $ accumTy step
                          (\T_pure   -> r)
                          (T_pure :: T_pure f xs)
    where
      step :: forall a as. T_pure f (a ': as) -> f a -> T_pure f as
      step _ _ = T_pure
  {-# INLINE pure  #-}
  (TFun f0 :: TFun f xs (a -> b)) <*> (TFun g0 :: TFun f xs a)
    = TFun $ accumTy (\(T_ap f g) a -> T_ap (f a) (g a))
                  (\(T_ap f g)   -> f g)
                  ( T_ap f0 g0 :: T_ap f (a -> b) a xs)
  {-# INLINE (<*>) #-}

newtype T_fmap f a   xs = T_fmap (Fn (Wrap f xs) a)
data    T_pure f     xs = T_pure
data    T_ap   f a b xs = T_ap (Fn (Wrap f xs) a) (Fn (Wrap f xs) b)
