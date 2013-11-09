{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE Rank2Types            #-}
-- |
-- CPS encoded heterogeneous vectors.
module Data.Vector.HFixed.Cont (
    -- * CPS-encoded vector
    -- ** Type classes
    Fn
  , Fun(..)
  , TFun(..)
  , Arity(..)
  , HVector(..)
  , HVectorF(..)
  , ValueAt
  , Index
  , Wrap
    -- ** CPS-encoded vector
  , ContVec(..)
  , ContVecF(..)
  , runContVec
    -- ** Other data types
  , VecList(..)
  , VecListF(..)
    -- ** Conversion to/from vector
  , cvec
  , vector
  , cvecF
  , vectorF
    -- * Constructors
  , mk0
  , mk1
  , mk2
  , mk3
  , mk4
  , mk5
    -- * Generic functions
  , head
  , tail
  , cons
  , concat
  , index
  , set
    -- * Map & zip
  , Apply(..)
  , Apply2(..)
  , Apply2Mono(..)
  , Map(..)
  , MapRes
  , map
  , Zip(..)
  , ZipRes
  , zipWith
  , ZipMono(..)
  , zipMono
  ) where

import Control.Applicative (Applicative(..))
import Prelude hiding (head,tail,concat,sequence,sequence_,map,zipWith)

import Data.Vector.HFixed.Class



----------------------------------------------------------------
-- Data
----------------------------------------------------------------

-- | CPS-encoded heterogeneous vector.
newtype ContVec xs = ContVec (forall r. Fun xs r -> r)

-- | Apply finalizer to continuation.
runContVec :: Fun xs r -> ContVec xs -> r
runContVec f (ContVec cont) = cont f
{-# INLINE runContVec #-}

instance Arity xs => HVector (ContVec xs) where
  type Elems (ContVec xs) = xs
  construct = Fun $
    accum (\(T_mkN f) x -> T_mkN (f . cons x))
          (\(T_mkN f)   -> f mk0)
          (T_mkN id :: T_mkN xs xs)
  inspect   = flip runContVec
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

newtype T_mkN all xs = T_mkN (ContVec xs -> ContVec all)


-- | CPS-encoded partially heterogeneous vector.
newtype ContVecF xs f = ContVecF (forall r. TFun f xs r -> r)

instance Arity xs => HVectorF (ContVecF xs) where
  type ElemsF (ContVecF xs) = xs
  inspectF (ContVecF cont) = cont
  constructF = constructFF
  {-# INLINE constructF #-}
  {-# INLINE inspectF   #-}

constructFF :: forall f xs. (Arity xs) => TFun f xs (ContVecF xs f)
{-# INLINE constructFF #-}
constructFF = TFun $ accumTy (\(TF_mkN f) x -> TF_mkN (f . consF x))
                             (\(TF_mkN f)   -> f $ ContVecF unTFun)
                             (TF_mkN id :: TF_mkN f xs xs)

newtype TF_mkN f all xs = TF_mkN (ContVecF xs f -> ContVecF all f)


----------------------------------------------------------------
-- Conversions between vectors
----------------------------------------------------------------

-- | Convert heterogeneous vector to CPS form
cvec :: (HVector v, Elems v ~ xs) => v -> ContVec xs
cvec v = ContVec (inspect v)
{-# INLINE cvec #-}

-- | Convert CPS-vector to heterogeneous vector
vector :: (HVector v, Elems v ~ xs) => ContVec xs -> v
vector = runContVec construct
{-# INLINE vector #-}

cvecF :: HVectorF v => v f -> ContVecF (ElemsF v) f
cvecF v = ContVecF (inspectF v)
{-# INLINE cvecF #-}

vectorF :: HVectorF v => ContVecF (ElemsF v) f -> v f
vectorF (ContVecF cont) = cont constructF
{-# INLINE vectorF #-}



----------------------------------------------------------------
-- Constructors
----------------------------------------------------------------

mk0 :: ContVec '[]
mk0 = ContVec $ \(Fun r) -> r
{-# INLINE mk0 #-}

mk1 :: a -> ContVec '[a]
mk1 a1 = ContVec $ \(Fun f) -> f a1
{-# INLINE mk1 #-}

mk2 :: a -> b -> ContVec '[a,b]
mk2 a1 a2 = ContVec $ \(Fun f) -> f a1 a2
{-# INLINE mk2 #-}

mk3 :: a -> b -> c -> ContVec '[a,b,c]
mk3 a1 a2 a3 = ContVec $ \(Fun f) -> f a1 a2 a3
{-# INLINE mk3 #-}

mk4 :: a -> b -> c -> d -> ContVec '[a,b,c,d]
mk4 a1 a2 a3 a4 = ContVec $ \(Fun f) -> f a1 a2 a3 a4
{-# INLINE mk4 #-}

mk5 :: a -> b -> c -> d -> e -> ContVec '[a,b,c,d,e]
mk5 a1 a2 a3 a4 a5 = ContVec $ \(Fun f) -> f a1 a2 a3 a4 a5
{-# INLINE mk5 #-}



----------------------------------------------------------------
-- Transformation
----------------------------------------------------------------

-- | Head of vector
head :: forall x xs. Arity xs => ContVec (x ': xs) -> x
head = runContVec $ Fun $ \x -> unFun (pure x :: Fun xs x)
{-# INLINE head #-}

-- | Tail of CPS-encoded vector
tail :: ContVec (x ': xs) -> ContVec xs
tail (ContVec cont) = ContVec $ cont . constFun
{-# INLINE tail #-}

-- | Cons element to the vector
cons :: x -> ContVec xs -> ContVec (x ': xs)
cons x (ContVec cont) = ContVec $ \f -> cont $ curryFun f x
{-# INLINE cons #-}

-- | Cons element to the vector
consF :: f x -> ContVecF xs f -> ContVecF (x ': xs) f
consF x (ContVecF cont) = ContVecF $ \f -> cont $ curryTFun f x
{-# INLINE consF #-}

-- | Concatenate two vectors
concat :: Arity xs => ContVec xs -> ContVec ys -> ContVec (xs ++ ys)
concat (ContVec contX) (ContVec contY) = ContVec $ contY . contX . curryMany
{-# INLINE concat #-}

-- | Get value at @n@th position.
index :: Index n xs => ContVec xs -> n -> ValueAt n xs
index (ContVec cont) = cont . getF
{-# INLINE index #-}

-- | Set value on nth position.
set :: Index n xs => n -> ValueAt n xs -> ContVec xs -> ContVec xs
set n x (ContVec cont) = ContVec $ cont . putF n x
{-# INLINE set #-}

map :: Map t xs => t -> ContVec xs -> ContVec (MapRes t xs)
{-# INLINE map #-}
map t (ContVec cont)
  = ContVec $ \fun -> cont $ mapF t fun


zipWith :: Zip t xs ys => t -> ContVec xs -> ContVec ys -> ContVec (ZipRes t xs ys)
{-# INLINE zipWith #-}
zipWith t (ContVec contX) (ContVec contY)
  = ContVec $ \fun -> contY $ contX $ zipF t fun

zipMono :: ZipMono t xs => t -> ContVec xs -> ContVec xs -> ContVec xs
{-# INLINE zipMono #-}
zipMono t (ContVec contX) (ContVec contY)
  = ContVec $ \fun -> contY $ contX $ zipMonoF t fun



----------------------------------------------------------------
-- Other vectors
----------------------------------------------------------------

-- | List like heterogeneous vector.
data VecList :: [*] -> * where
  Nil  :: VecList '[]
  Cons :: x -> VecList xs -> VecList (x ': xs)

instance Arity xs => HVector (VecList xs) where
  type Elems (VecList xs) = xs
  construct = Fun $ accum
    (\(T_List f) a -> T_List (f . Cons a))
    (\(T_List f)   -> f Nil)
    (T_List id :: T_List xs xs)
  inspect v (Fun f) = apply step v f
    where
      step :: VecList (a ': as) -> (a, VecList as)
      step (Cons a xs) = (a, xs)
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

newtype T_List all xs = T_List (VecList xs -> VecList all)


-- | List-like vector
data VecListF xs f where
  NilF  :: VecListF '[] f
  ConsF :: f x -> VecListF xs f -> VecListF (x ': xs) f

instance Arity xs => HVectorF (VecListF xs) where
  type ElemsF (VecListF xs) = xs
  constructF = conVecF
  inspectF v (TFun f) = applyTy step (TF_insp v) f
    where
      step :: TF_insp f (a ': as) -> (f a, TF_insp f as)
      step (TF_insp (ConsF a xs)) = (a, TF_insp xs)
  {-# INLINE constructF #-}
  {-# INLINE inspectF   #-}

conVecF :: forall f xs. (Arity xs) => TFun f xs (VecListF xs f)
conVecF = TFun $ accumTy (\(TF_List f) a -> TF_List (f . ConsF a))
                         (\(TF_List f)   -> f NilF)
                         (TF_List id :: TF_List f xs xs)

newtype TF_insp f     xs = TF_insp (VecListF xs f)
newtype TF_List f all xs = TF_List (VecListF xs f -> VecListF all f)
