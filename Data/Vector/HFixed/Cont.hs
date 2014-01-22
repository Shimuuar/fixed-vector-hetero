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
  , Implicit(..)
  , ValueAt
  , Index
  , Wrap
    -- ** CPS-encoded vector
  , ContVec(..)
  , ContVecF(..)
  , toContVec
  , toContVecF
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
  , consF
  , concat
  , index
  , set
    -- * Working with monads\/applicative
  , mapFunctor
  , sequence
  , sequenceA
  , sequenceF
  , sequenceAF
  , distribute
  , distributeF
  , wrap
  , unwrap
    -- * More
  , replicate
  , replicateM
  , foldl
  , foldr
  , unfoldr
  , zipMono
  , zipFold
  , monomorphize
  ) where

import Control.Applicative   (Applicative(..))
import Control.Monad         (ap)
import Data.Monoid           (Monoid(..),(<>))
import Data.Functor.Compose  (Compose(..))
import qualified Data.Vector.Fixed.Cont as F
import Prelude hiding
  (head,tail,concat,sequence,sequence_,map,zipWith,
   replicate,foldr,foldl)

import Data.Vector.HFixed.Class



----------------------------------------------------------------
-- Conversions between vectors
----------------------------------------------------------------

-- | Convert heterogeneous vector to CPS form
cvec :: (HVector v, Elems v ~ xs) => v -> ContVec xs
cvec v = ContVec (inspect v)
{-# INLINE cvec #-}

-- | Convert CPS-vector to heterogeneous vector
vector :: (HVector v, Elems v ~ xs) => ContVec xs -> v
vector (ContVec cont) = cont construct
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
head = flip inspect $ Fun $ \x -> unFun (pure x :: Fun xs x)
{-# INLINE head #-}

-- | Tail of CPS-encoded vector
tail :: ContVec (x ': xs) -> ContVec xs
tail (ContVec cont) = ContVec $ cont . constFun
{-# INLINE tail #-}

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


----------------------------------------------------------------
-- Monadic/applicative API
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



distribute :: forall f xs. (Arity xs, Functor f)
            => f (ContVec xs) -> ContVecF xs f
{-# INLINE distribute #-}
distribute f0
  = ContVecF $ \(TFun fun) -> applyTy step start fun
  where
    step :: forall a as. T_distribute f (a ': as) -> (f a, T_distribute f as)
    step (T_distribute v) = ( fmap (\(Cons x _) -> x) v
                            , T_distribute $ fmap (\(Cons _ x) -> x) v
                            )
    start :: T_distribute f xs
    start = T_distribute $ fmap vector f0

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

newtype T_distribute    f xs = T_distribute  (f (VecList  xs))
newtype T_distributeF f g xs = T_distributeF (f (VecListF xs g))



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
  inspect = runContVec . apply step
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



----------------------------------------------------------------
-- More combinators
----------------------------------------------------------------

-- | Replicate value n times.
replicate :: forall xs c. (ArityC c xs)
          => Proxy c -> (forall x. c x => x) -> ContVec xs
{-# INLINE replicate #-}
replicate _ x
  = apply (\(WitAllInstancesCons d) -> (x,d))
          (witAllInstances :: WitAllInstances c xs)


-- | Replicate monadic action n times.
replicateM :: forall xs c m. (ArityC c xs, Monad m)
           => Proxy c -> (forall x. c x => m x) -> m (ContVec xs)
{-# INLINE replicateM #-}
replicateM _ act = do
  applyM (\(WitAllInstancesCons d) -> do{ x <- act; return (x,d)})
         (witAllInstances :: WitAllInstances c xs)

-- | Right fold over vector
foldr :: forall xs c b. (ArityC c xs)
      => Proxy c -> (forall a. c a => a -> b -> b) -> b -> ContVec xs -> b
{-# INLINE foldr #-}
foldr _ f b0 v
  = inspect v $ Fun
  $ accum (\(T_foldr b (WitAllInstancesCons d)) a -> T_foldr (b . f a) d)
          (\(T_foldr b  _                     )   -> b b0)
          (T_foldr id witAllInstances :: T_foldr c b xs)

-- | Left fold over vector
foldl :: forall xs c b. (ArityC c xs)
      => Proxy c -> (forall a. c a => b -> a -> b) -> b -> ContVec xs -> b
{-# INLINE foldl #-}
foldl _ f b0 v
  = inspect v $ Fun
  $ accum (\(T_foldl b (WitAllInstancesCons d)) a -> T_foldl (f b a) d)
          (\(T_foldl b  _                     )   -> b)
          (T_foldl b0 witAllInstances :: T_foldl c b xs)

data T_foldr c b xs = T_foldr (b -> b) (WitAllInstances c xs)
data T_foldl c b xs = T_foldl  b       (WitAllInstances c xs)


-- | Convert heterogeneous vector to homogeneous
monomorphize :: forall c xs a. (ArityC c xs)
             => Proxy c -> (forall x. c x => x -> a)
             -> ContVec xs -> F.ContVec (Len xs) a
{-# INLINE monomorphize #-}
monomorphize _ f v
  = inspect v $ Fun $ accum
      (\(T_mono cont (WitAllInstancesCons d)) a -> T_mono (cont . F.cons (f a)) d)
      (\(T_mono cont _)                         -> cont F.empty)
      (T_mono id witAllInstances :: T_mono c a xs xs)


data T_mono c a all xs = T_mono (F.ContVec (Len xs) a -> F.ContVec (Len all) a) (WitAllInstances c xs)

-- | Unfold vector.
unfoldr :: forall xs c b. (ArityC c xs)
        => Proxy c -> (forall a. c a => b -> (a,b)) -> b -> ContVec xs
{-# INLINE unfoldr #-}
unfoldr _ f b0 = apply
  (\(T_unfoldr b (WitAllInstancesCons d)) -> let (a,b') = f b
                                             in  (a,T_unfoldr b' d))
  (T_unfoldr b0 witAllInstances :: T_unfoldr c b xs)


data T_unfoldr c b xs = T_unfoldr b (WitAllInstances c xs)


-- | Zip two heterogeneous vectors
zipMono :: forall xs c. (ArityC c xs)
        => Proxy c -> (forall a. c a => a -> a -> a) -> ContVec xs -> ContVec xs -> ContVec xs
{-# INLINE zipMono #-}
zipMono _ f cvecA cvecB
  = apply (\(T_zipMono (Cons a va) (Cons b vb) (WitAllInstancesCons w)) ->
              (f a b, T_zipMono va vb w))
          (T_zipMono (vector cvecA) (vector cvecB) witAllInstances :: T_zipMono c xs)

data T_zipMono c xs = T_zipMono (VecList xs) (VecList xs) (WitAllInstances c xs)


-- | Zip vector and fold result using monoid
zipFold :: forall xs c m. (ArityC c xs, Monoid m)
        => Proxy c -> (forall a. c a => a -> a -> m) -> ContVec xs -> ContVec xs -> m
{-# INLINE zipFold #-}
zipFold _ f cvecA cvecB
  = inspect cvecB zipF
  where
    zipF :: Fun xs m
    zipF = Fun $ accum (\(T_zipFold (Cons a va) m (WitAllInstancesCons w)) b ->
                           T_zipFold va (m <> f a b) w)
                       (\(T_zipFold _ m _) -> m)
                       (T_zipFold (vector cvecA) mempty witAllInstances :: T_zipFold c m xs)

data T_zipFold c m xs = T_zipFold (VecList xs) m (WitAllInstances c xs)


