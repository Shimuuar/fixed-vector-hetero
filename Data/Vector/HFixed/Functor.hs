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
module Data.Vector.HFixed.Functor (
    -- * Data types and type classes
    Fn
  , Fun(..)
  , TFun(..)
  , Arity
  , HVectorF(..)
    -- * CPS-encoded vector
  , ContVecF(..)
  , cvecF
  , vectorF
  , toContVec
  , toContVecF
    -- ** Function on CPS-encoded vector
    -- *** Constructor
  -- , mk0
  -- , mk1
  -- , mk2
  -- , mk3
  -- , mk4
  -- , mk5
    -- *** Other
  -- , cons
  , mapFunctor
  , sequence
  , sequenceA
  , sequenceF
  , sequenceAF
  , distribute
  , distributeF
  , wrap
  , unwrap
  ) where

import Control.Applicative   (Applicative(..))
import Control.Monad         (ap)
import Data.Functor.Compose  (Compose(..))

import Data.Vector.HFixed.Class
import qualified Data.Vector.HFixed.Cont as C
import           Data.Vector.HFixed.Cont

import Prelude hiding (sequence)



----------------------------------------------------------------
-- Data types
----------------------------------------------------------------


toContVec :: ContVecF xs f -> ContVec (Wrap f xs)
toContVec (ContVecF cont) = ContVec $ cont . TFun . unFun
{-# INLINE toContVec #-}

toContVecF :: ContVec (Wrap f xs) -> ContVecF xs f
toContVecF (ContVec cont) = ContVecF $ cont . Fun . unTFun
{-# INLINE toContVecF #-}



----------------------------------------------------------------
-- Functions
----------------------------------------------------------------

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


----------------------------------------------------------------
-- Map
----------------------------------------------------------------

-- | Map functor.
mapFunctor :: (Arity xs)
     => (forall a. f a -> g a) -> ContVecF xs f -> ContVecF xs g
mapFunctor f (ContVecF cont) = ContVecF $ cont . mapFF f
{-# INLINE mapFunctor #-}

mapFF :: forall r f g xs. (Arity xs)
      => (forall a. f a -> g a) -> TFun g xs r -> TFun f xs r
{-# INLINE mapFF #-}
mapFF g (TFun f0) = TFun $ accumTy
  (\(TF_map f) a -> TF_map $ f (g a))
  (\(TF_map r)   -> r)
  (TF_map f0 :: TF_map r g xs)

newtype TF_map r g xs = TF_map (Fn (Wrap g xs) r)


----------------------------------------------------------------
-- Sequence
----------------------------------------------------------------

-- | Sequence vector's elements
sequence :: (Arity xs, Monad m)
          => ContVecF xs m -> m (ContVec xs)
sequence (ContVecF cont)
  = cont $ sequence_F construct
{-# INLINE sequence #-}

-- | Sequence vector's elements
sequenceA :: (Arity xs, Applicative f)
          => ContVecF xs f -> f (ContVec xs)
sequenceA (ContVecF cont)
  = cont $ sequenceA_F construct
{-# INLINE sequenceA #-}

-- | Sequence vector's elements
sequenceF :: (Arity xs, Monad m)
          => ContVecF xs (m `Compose` f) -> m (ContVecF xs f)
sequenceF (ContVecF cont)
  = cont $ sequenceF_F constructF
{-# INLINE sequenceF #-}

-- | Sequence vector's elements
sequenceAF :: (Arity xs, Applicative f)
           => ContVecF xs (f `Compose` g) -> f (ContVecF xs g)
sequenceAF (ContVecF cont)
  = cont $ sequenceAF_F constructF
{-# INLINE sequenceAF #-}


sequence_F :: forall m xs r. (Monad m, Arity xs)
          => Fun xs r -> TFun m xs (m r)
{-# INLINE sequence_F #-}
sequence_F (Fun f) = TFun $
  accumTy (\(T_seq m) a -> T_seq $ m `ap` a)
          (\(T_seq m)             -> m)
          (T_seq (return f) :: T_seq m r xs)

sequenceA_F :: forall f xs r. (Applicative f, Arity xs)
          => Fun xs r -> TFun f xs (f r)
{-# INLINE sequenceA_F #-}
sequenceA_F (Fun f) = TFun $
  accumTy (\(T_seq m) a -> T_seq $ m <*> a)
          (\(T_seq m)             -> m)
          (T_seq (pure f) :: T_seq f r xs)

sequenceAF_F :: forall f g xs r. (Applicative f, Arity xs)
          => TFun g xs r -> TFun (f `Compose` g) xs (f r)
{-# INLINE sequenceAF_F #-}
sequenceAF_F (TFun f) = TFun $
  accumTy (\(T_seq2 m) (Compose a) -> T_seq2 $ m <*> a)
          (\(T_seq2 m)             -> m)
          (T_seq2 (pure f) :: T_seq2 f g r xs)

sequenceF_F :: forall m f xs r. (Monad m, Arity xs)
          => TFun f xs r -> TFun (m `Compose` f) xs (m r)
{-# INLINE sequenceF_F #-}
sequenceF_F (TFun f) = TFun $
  accumTy (\(T_seq2 m) (Compose a) -> T_seq2 $ m `ap` a)
          (\(T_seq2 m)             -> m)
          (T_seq2 (return f) :: T_seq2 m f r xs)


newtype T_seq    f r xs = T_seq  (f (Fn xs r))
newtype T_seq2 f g r xs = T_seq2 (f (Fn (Wrap g xs) r))



----------------------------------------------------------------
-- Distribute
----------------------------------------------------------------

distribute :: forall f xs. (Arity xs, Functor f)
            => f (ContVec xs) -> ContVecF xs f
{-# INLINE distribute #-}
distribute f0
  = ContVecF $ \(TFun fun) -> applyTy step start fun
  where
    step :: forall a as. T_distribute f (a ': as) -> (f a, T_distribute f as)
    step (T_distribute v) = ( fmap (\(C.Cons x _) -> x) v
                            , T_distribute $ fmap (\(C.Cons _ x) -> x) v
                            )
    start :: T_distribute f xs
    start = T_distribute $ fmap C.vector f0

distributeF :: forall f g xs. (Arity xs, Functor f)
            => f (ContVecF xs g) -> ContVecF xs (f `Compose` g)
{-# INLINE distributeF #-}
distributeF f0
  = ContVecF $ \(TFun fun) -> applyTy step start fun
  where
    step :: forall a as. T_distributeF f g (a ': as) -> ((Compose f g) a, T_distributeF f g as)
    step (T_distributeF v) = ( Compose $ fmap (\(ConsF x _) -> x) v
                             , T_distributeF $ fmap (\(ConsF _ x) -> x) v
                             )
    start :: T_distributeF f g xs
    start = T_distributeF $ fmap vectorF f0

newtype T_distribute    f xs = T_distribute  (f (C.VecList xs))
newtype T_distributeF f g xs = T_distributeF (f (VecListF xs g))



----------------------------------------------------------------
-- Wrap & unwrap
----------------------------------------------------------------

-- | Wrap every value in the vector into type constructor.
wrap :: Arity xs => (forall a. a -> f a) -> ContVec xs -> ContVecF xs f
{-# INLINE wrap #-}
wrap f (ContVec cont)
  = ContVecF $ \fun -> cont $ wrapF f fun

wrapF :: forall f xs r. (Arity xs)
       => (forall a. a -> f a) -> TFun f xs r -> Fun xs r
{-# INLINE wrapF #-}
wrapF g (TFun f0) = Fun $ accum (\(T_wrap f) x -> T_wrap $ f (g x))
                                (\(T_wrap r)   -> r)
                                (T_wrap f0 :: T_wrap f r xs)

newtype T_wrap f r xs = T_wrap (Fn (Wrap f xs) r)

-- | Unwrap every value in the vector from the type constructor.
unwrap :: Arity xs => (forall a. f a -> a) -> ContVecF xs f -> ContVec xs
{-# INLINE unwrap #-}
unwrap f (ContVecF cont)
  = ContVec $ \fun -> cont $ unwrapF f fun

unwrapF :: forall f xs r. (Arity xs)
         => (forall a. f a -> a) -> Fun xs r -> TFun f xs r
{-# INLINE unwrapF #-}
unwrapF g (Fun f0) = TFun $ accumTy (\(T_unwrap f) x -> T_unwrap $ f (g x))
                                    (\(T_unwrap r)   -> r)
                                    (T_unwrap f0 :: T_unwrap r xs)

newtype T_unwrap r xs = T_unwrap (Fn xs r)
