{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE UndecidableInstances  #-}
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
  -- , toContVec
  -- , toContVecF
    -- ** Other data types
  , VecList(..)
  , VecListF(..)
    -- * Conversion to/from vector
  , cvec
  , vector
  , cvecF
  , vectorF
    -- * Position based functions
  , head
  , tail
  , cons
  , consF
  , concat
    -- * Indexing
  , index
  , set
    -- * Constructors
  , mk0
  , mk1
  , mk2
  , mk3
  , mk4
  , mk5
    -- * Folds and unfolds
  , foldl
  , foldr
  , unfoldr
    -- * Polymorphic values
  , replicate
  , replicateM
  , replicateF
  , replicateF'
  , zipMono
  , zipMonoF
  , zipFold
  , zipNatF
  -- , monomorphize
  -- , monomorphizeF
    -- * Vector parametrized with type constructor
  , mapFunctor
  , sequence
  , sequenceF
  , distribute
  , distributeF
  , wrap
  , unwrap
  ) where

import Control.Applicative   (Applicative(..))
import Data.Coerce           (coerce)
import Data.Monoid           (Monoid(..),(<>))
import Data.Functor.Compose  (Compose(..))
import Data.Functor.Identity (Identity(..))
import Data.Typeable         (Proxy(..))
import qualified Data.Vector.Fixed.Cont as F
import Prelude               (Functor(..),id,(.),($),undefined)

import Data.Vector.HFixed.Class



----------------------------------------------------------------
-- Conversions between vectors
----------------------------------------------------------------

-- | Convert heterogeneous vector to CPS form
cvec :: (HVector v, Elems v ~ xs) => v -> ContVec xs
cvec v = ContVecF (inspect v)
{-# INLINE cvec #-}

-- | Convert CPS-vector to heterogeneous vector
vector :: (HVector v, Elems v ~ xs) => ContVec xs -> v
vector (ContVecF cont) = cont construct
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
mk0 = ContVecF unTFun
{-# INLINE mk0 #-}

mk1 :: a -> ContVec '[a]
mk1 a1 = ContVecF $ \f -> coerce f a1
{-# INLINE mk1 #-}

mk2 :: a -> b -> ContVec '[a,b]
mk2 a1 a2 = ContVecF $ \f -> coerce f a1 a2
{-# INLINE mk2 #-}

mk3 :: a -> b -> c -> ContVec '[a,b,c]
mk3 a1 a2 a3 = ContVecF $ \f -> coerce f a1 a2 a3
{-# INLINE mk3 #-}

mk4 :: a -> b -> c -> d -> ContVec '[a,b,c,d]
mk4 a1 a2 a3 a4 = ContVecF $ \f -> coerce f a1 a2 a3 a4
{-# INLINE mk4 #-}

mk5 :: a -> b -> c -> d -> e -> ContVec '[a,b,c,d,e]
mk5 a1 a2 a3 a4 a5 = ContVecF $ \f -> coerce f a1 a2 a3 a4 a5
{-# INLINE mk5 #-}



----------------------------------------------------------------
-- Transformation
----------------------------------------------------------------

-- | Head of vector
head :: forall x xs. Arity xs => ContVec (x : xs) -> x
head v = inspect v (uncurryFun pure)
{-# INLINE head #-}

-- | Tail of CPS-encoded vector
tail :: ContVec (x : xs) -> ContVec xs
tail (ContVecF cont) = ContVecF $ cont . constFun
{-# INLINE tail #-}

-- | Concatenate two vectors
concat :: Arity xs => ContVec xs -> ContVec ys -> ContVec (xs ++ ys)
concat (ContVecF contX) (ContVecF contY) = ContVecF $ contY . contX . curryMany
{-# INLINE concat #-}

-- | Get value at @n@th position.
index :: Index n xs => ContVec xs -> n -> ValueAt n xs
index (ContVecF cont) = cont . getF
{-# INLINE index #-}

-- | Set value on nth position.
set :: Index n xs => n -> ValueAt n xs -> ContVec xs -> ContVec xs
set n x (ContVecF cont) = ContVecF $ cont . putF n x
{-# INLINE set #-}


----------------------------------------------------------------
-- Monadic/applicative API
----------------------------------------------------------------

-- | Apply natural transformation to every element of the tuple.
mapFunctor :: (Arity xs)
     => (forall a. f a -> g a) -> ContVecF xs f -> ContVecF xs g
mapFunctor f (ContVecF cont) = ContVecF $ cont . mapFF f
{-# INLINE mapFunctor #-}

mapFF :: forall r f g xs. (Arity xs)
      => (forall a. f a -> g a) -> TFun g xs r -> TFun f xs r
{-# INLINE mapFF #-}
mapFF g (TFun f0) = accum
  (\(TF_map f) a -> TF_map $ f (g a))
  (\(TF_map r)   -> r)
  (TF_map f0)

newtype TF_map r g xs = TF_map (Fn g xs r)



-- | Sequence vector's elements
sequence :: (Arity xs, Applicative f)
         => ContVecF xs f -> f (ContVec xs)
sequence = sequenceF
         . mapFunctor (Compose . fmap Identity)
{-# INLINE sequence #-}

-- | Sequence vector's elements
sequenceF :: (Arity xs, Applicative f)
          => ContVecF xs (f `Compose` g) -> f (ContVecF xs g)
sequenceF (ContVecF cont)
  = cont $ sequenceF_F constructF
{-# INLINE sequenceF #-}


sequenceF_F :: forall f g xs r. (Applicative f, Arity xs)
            => TFun g xs r -> TFun (f `Compose` g) xs (f r)
{-# INLINE sequenceF_F #-}
sequenceF_F (TFun f) =
  accum (\(T_seq2 m) (Compose a) -> T_seq2 $ m <*> a)
        (\(T_seq2 m)             -> m)
        (T_seq2 (pure f))

newtype T_seq2 f g r xs = T_seq2 (f (Fn g xs r))



distribute :: forall f xs. (Arity xs, Functor f)
            => f (ContVec xs) -> ContVecF xs f
{-# INLINE distribute #-}
distribute f0
  = apply step start
  where
    step :: forall a as. T_distribute f (a : as) -> (f a, T_distribute f as)
    step (T_distribute v) = ( fmap (\(Cons x _) -> x) v
                            , T_distribute $ fmap (\(Cons _ x) -> x) v
                            )
    start :: T_distribute f xs
    start = T_distribute $ fmap vector f0

distributeF :: forall f g xs. (Arity xs, Functor f)
            => f (ContVecF xs g) -> ContVecF xs (f `Compose` g)
{-# INLINE distributeF #-}
distributeF f0
  = apply step start
  where
    step :: forall a as. T_distributeF f g (a : as) -> ((Compose f g) a, T_distributeF f g as)
    step (T_distributeF v) = ( Compose $ fmap (\(ConsF x _) -> x) v
                             , T_distributeF $ fmap (\(ConsF _ x) -> x) v
                             )
    start :: T_distributeF f g xs
    start = T_distributeF $ fmap vectorF f0

newtype T_distribute    f xs = T_distribute  (f (VecList  xs))
newtype T_distributeF f g xs = T_distributeF (f (VecListF xs g))



-- | Wrap every value in the vector into type constructor.
wrap :: Arity xs => (forall a. a -> f a) -> ContVec xs -> ContVecF xs f
{-# INLINE wrap #-}
wrap f = mapFunctor (f . runIdentity)

-- | Unwrap every value in the vector from the type constructor.
unwrap :: Arity xs => (forall a. f a -> a) -> ContVecF xs f -> ContVec xs
{-# INLINE unwrap #-}
unwrap f = mapFunctor (Identity . f)




----------------------------------------------------------------
-- Other vectors
----------------------------------------------------------------

-- | List like heterogeneous vector.
data VecList :: [*] -> * where
  Nil  :: VecList '[]
  Cons :: x -> VecList xs -> VecList (x : xs)

instance Arity xs => HVector (VecList xs) where
  type Elems (VecList xs) = xs
  construct = accum
    (\(T_List f) (Identity a) -> T_List (f . Cons a))
    (\(T_List f)              -> f Nil)
    (T_List id)
  inspect = runContVecF . apply step
    where
      step :: VecList (a : as) -> (Identity a, VecList as)
      step (Cons a xs) = (Identity a, xs)
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

newtype T_List all xs = T_List (VecList xs -> VecList all)


-- | List-like vector
data VecListF xs f where
  NilF  :: VecListF '[] f
  ConsF :: f x -> VecListF xs f -> VecListF (x : xs) f

instance Arity xs => HVectorF (VecListF xs) where
  type ElemsF (VecListF xs) = xs
  constructF   = conVecF
  inspectF   v = inspectF (apply step (TF_insp v))
    where
      step :: TF_insp f (a : as) -> (f a, TF_insp f as)
      step (TF_insp (ConsF a xs)) = (a, TF_insp xs)
  {-# INLINE constructF #-}
  {-# INLINE inspectF   #-}

conVecF :: forall f xs. (Arity xs) => TFun f xs (VecListF xs f)
conVecF = accum (\(TF_List f) a -> TF_List (f . ConsF a))
                (\(TF_List f)   -> f NilF)
                (TF_List id)

newtype TF_insp f     xs = TF_insp (VecListF xs f)
newtype TF_List f all xs = TF_List (VecListF xs f -> VecListF all f)



----------------------------------------------------------------
-- More combinators
----------------------------------------------------------------

-- | Replicate polymorphic value n times. Concrete instance for every
--   element is determined by their respective types.
replicate :: forall xs c. (ArityC c xs)
          => Proxy c -> (forall x. c x => x) -> ContVec xs
{-# INLINE replicate #-}
replicate cls x
  = applyC cls (\Proxy -> (Identity x,Proxy)) Proxy

-- | Replicate monadic action n times.
replicateM :: (ArityC c xs, Applicative f)
           => Proxy c -> (forall a. c a => f a) -> f (ContVec xs)
{-# INLINE replicateM #-}
replicateM p x = sequence (replicateF' p x)

replicateF :: forall f xs. Arity xs => (forall a. f a) -> ContVecF xs f
{-# INLINE replicateF #-}
replicateF f = apply (\Proxy -> (f, Proxy)) (Proxy)

replicateF' :: forall f c xs. ArityC c xs => Proxy c -> (forall a. c a => f a) -> ContVecF xs f
{-# INLINE replicateF' #-}
replicateF' cls f = applyC cls (\Proxy -> (f,Proxy)) Proxy


-- | Right fold over vector
foldr :: forall xs c b. (ArityC c xs)
      => Proxy c -> (forall a. c a => a -> b -> b) -> b -> ContVec xs -> b
{-# INLINE foldr #-}
foldr cls f b0 v
  = inspect v
  $ accumC cls (\(T_foldr b) (Identity a) -> T_foldr (b . f a))
               (\(T_foldr b)              -> b b0)
               (T_foldr id :: T_foldr b xs)

-- | Left fold over vector
foldl :: forall xs c b. (ArityC c xs)
      => Proxy c -> (forall a. c a => b -> a -> b) -> b -> ContVec xs -> b
{-# INLINE foldl #-}
foldl cls f b0 v
  = inspect v
  $ accumC cls (\(T_foldl b) (Identity a) -> T_foldl (f b a))
               (\(T_foldl b)              -> b)
               (T_foldl b0 :: T_foldl b xs)

data T_foldr b xs = T_foldr (b -> b)
data T_foldl b xs = T_foldl  b


-- -- | Convert heterogeneous vector to homogeneous
-- monomorphize :: forall c xs a. (ArityC c xs)
--              => Proxy c -> (forall x. c x => x -> a)
--              -> ContVec xs -> F.ContVec (Len xs) a
-- {-# INLINE monomorphize #-}
-- monomorphize _ f v
--   = inspect v $ accum
--       (\(T_mono cont (WitAllInstancesCons d)) a -> T_mono (cont . F.cons (f a)) d)
--       (\(T_mono cont _)                         -> cont F.empty)
--       (T_mono id witAllInstances :: T_mono c a xs xs)

-- -- | Convert heterogeneous vector to homogeneous
-- monomorphizeF :: forall c xs a f. (ArityC c xs)
--               => Proxy c -> (forall x. c x => f x -> a)
--               -> ContVecF xs f -> F.ContVec (Len xs) a
-- {-# INLINE monomorphizeF #-}
-- monomorphizeF _ f v
--   = inspectF v $ accumTy step fini start
--   where
--     step :: forall z zs. T_mono c a xs (z : zs) -> f z -> T_mono c a xs zs
--     step (T_mono cont (WitAllInstancesCons d)) a = T_mono (cont . F.cons (f a)) d
--     --
--     fini (T_mono cont _) = cont F.empty
--     start = (T_mono id witAllInstances :: T_mono c a xs xs)

-- data T_mono c a all xs = T_mono (F.ContVec (Len xs) a -> F.ContVec (Len all) a) (WitAllInstances c xs)


-- | Unfold vector.
unfoldr :: forall xs c b. (ArityC c xs)
        => Proxy c -> (forall a. c a => b -> (a,b)) -> b -> ContVec xs
{-# INLINE unfoldr #-}
unfoldr cls f b0 = applyC cls
  (\(T_unfoldr b) -> let (a,b') = f b
                     in  (Identity a, T_unfoldr b'))
  (T_unfoldr b0 :: T_unfoldr b xs)

data T_unfoldr b xs = T_unfoldr b


-- | Zip two heterogeneous vectors
zipMono :: forall xs c. (ArityC c xs)
        => Proxy c -> (forall a. c a => a -> a -> a) -> ContVec xs -> ContVec xs -> ContVec xs
{-# INLINE zipMono #-}
zipMono cls f cvecA cvecB
  = applyC cls
    (\(T_zipMono (Cons a va) (Cons b vb)) ->
        ( Identity (f a b) , T_zipMono va vb ))
    (T_zipMono (vector cvecA) (vector cvecB) :: T_zipMono xs)

data T_zipMono xs = T_zipMono (VecList xs) (VecList xs)

-- | Zip two heterogeneous vectors
zipMonoF :: forall xs f g h c. (ArityC c xs)
         => Proxy c
         -> (forall a. c a => f a -> g a -> h a)
         -> ContVecF xs f
         -> ContVecF xs g
         -> ContVecF xs h
{-# INLINE zipMonoF #-}
zipMonoF cls f cvecA cvecB = applyC cls
  (\(T_zipMonoF (ConsF a va) (ConsF b vb)) ->
      (f a b, T_zipMonoF va vb))
  (T_zipMonoF (vectorF cvecA) (vectorF cvecB) :: T_zipMonoF f g xs)

data T_zipMonoF f g xs = T_zipMonoF (VecListF xs f) (VecListF xs g)


-- | Zip vector and fold result using monoid
zipFold :: forall xs c m. (ArityC c xs, Monoid m)
        => Proxy c -> (forall a. c a => a -> a -> m) -> ContVec xs -> ContVec xs -> m
{-# INLINE zipFold #-}
zipFold cls f cvecA cvecB
  = inspect cvecB zipF
  where
    zipF :: Fun xs m
    zipF = accumC cls
      (\(T_zipFold (Cons a va) m) (Identity b) -> T_zipFold va (m <> f a b))
      (\(T_zipFold _           m)              -> m)
      (T_zipFold (vector cvecA) mempty :: T_zipFold m xs)

data T_zipFold m xs = T_zipFold (VecList xs) m


-- | Zip two heterogeneous vectors
zipNatF :: forall xs f g h. (Arity xs)
        => (forall a. f a -> g a -> h a)
        -> ContVecF xs f
        -> ContVecF xs g
        -> ContVecF xs h
{-# INLINE zipNatF #-}
zipNatF f cvecA cvecB
  = apply (\(T_zipNatF (ConsF a va) (ConsF b vb)) -> (f a b, T_zipNatF va vb))
          (T_zipNatF (vectorF cvecA) (vectorF cvecB) :: T_zipNatF f g xs)

data T_zipNatF f g xs = T_zipNatF (VecListF xs f) (VecListF xs g)
