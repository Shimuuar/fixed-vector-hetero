{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE PolyKinds             #-}
module Data.Vector.HFixed (
    -- * Basic API
    Fn
  , Fun(..)
  , HVector(..)
    -- ** List length
  , Proxy(..)
  , ListLen(..)
    -- * Generic functions
  , convert
  , head
  , tail
  , cons
    -- * Generic constructors
  , mk0
  , mk1
  , mk2
  , mk3
  , mk4
  , mk5
    -- * Generic heterogeneous vector
  , HVec
  ) where

import Control.Monad.ST     (ST,runST)
import Data.Primitive.Array (Array,MutableArray,newArray,writeArray,indexArray,
                             unsafeFreezeArray
                            )
import GHC.Prim             (Any)
import Unsafe.Coerce        (unsafeCoerce)
import Prelude hiding (head,tail)


----------------------------------------------------------------
-- Type classes
----------------------------------------------------------------

-- | Type family for N-ary function. Types of function parameters are
--   encoded as the list of types.
type family Fn (as ::[*]) b
type instance Fn '[]       b = b
type instance Fn (a ': as) b = a -> Fn as b


-- | Newtype wrapper to work around of type families' lack of
--   injectivity.
newtype Fun (as :: [*]) b = Fun { unFun :: Fn as b }

instance Functor (Fun '[]) where
  fmap f (Fun x) = Fun (f x)

instance Functor (Fun xs) => Functor (Fun (x ': xs)) where
  fmap (f :: a -> b) (Fun g)
    = Fun $ \a -> unFun $ fmap f (Fun (g a) :: Fun xs a)


-- | Type class for heterogeneous vectors. Instance should specify way
-- to construct and deconstruct itself
--
-- Note that this type class is extremely generic. Almost any single
-- constructor data type could be made instance. It could be
-- monomorphic, it could be polymorphic in some or all fields it
-- doesn't matter. Only law instance should obey is:
--
-- > inspect v construct = v
class HVector v where
  type Elems v :: [*]
  construct :: Fun (Elems v) v
  inspect   :: v -> Fun (Elems v) a -> a


data Proxy (a :: α) = Proxy

class ListLen (xs :: [*]) where
  listLen :: Proxy xs -> Int

instance ListLen '[] where
  listLen _ = 0
instance ListLen xs => ListLen (x ': xs) where
  listLen _ = 1 + listLen (Proxy :: Proxy xs)



----------------------------------------------------------------
-- Generic API
----------------------------------------------------------------

-- | We can convert between any two vector which have same
--   structure but different representations.
convert :: (HVector v, HVector w, Elems v ~ Elems w)
        => v -> w
{-# INLINE convert #-}
convert v = inspect v construct

-- | Tail of the vector
--
-- >>> case tail ('a',"aa",()) of x@(_,_) -> x
-- ("aa",())
tail :: forall a v w. (HVector v, HVector w, (a ': Elems w) ~ Elems v)
     => v -> w
{-# INLINE tail #-}
tail v = inspect v
       $ Fun $ const $ unFun (construct :: Fun (Elems w) w)

-- | Head of the vector
head :: forall a as v. (HVector v, Elems v ~ (a ': as), ConstF as)
     => v -> a
{-# INLINE head #-}
head v = inspect v
       $ Fun (\a -> unFun (constF a :: Fun as a))

-- | Prepend element to the list
cons :: forall a v w. (HVector v, HVector w, Elems w ~ (a ': Elems v))
     => a -> v -> w
{-# INLINE cons #-}
cons a v = inspect v
       $ Fun $ unFun (construct :: Fun (Elems w) w) a



----------------------------------------------------------------
-- Constructors
----------------------------------------------------------------

mk0 :: forall v. (HVector v, Elems v ~ '[]) => v
mk0 = unFun (construct :: Fun (Elems v) v)

mk1 :: forall v a. (HVector v, Elems v ~ '[a]) => a -> v
mk1 a = unFun (construct :: Fun (Elems v) v) a

mk2 :: forall v a b. (HVector v, Elems v ~ '[a,b]) => a -> b -> v
mk2 a b = unFun (construct :: Fun (Elems v) v) a b

mk3 :: forall v a b c. (HVector v, Elems v ~ '[a,b,c]) => a -> b -> c -> v
mk3 a b c = unFun (construct :: Fun (Elems v) v) a b c

mk4 :: forall v a b c d. (HVector v, Elems v ~ '[a,b,c,d]) => a -> b -> c -> d -> v
mk4 a b c d = unFun (construct :: Fun (Elems v) v) a b c d

mk5 :: forall v a b c d e. (HVector v, Elems v ~ '[a,b,c,d,e]) => a -> b -> c -> d -> e -> v
mk5 a b c d e = unFun (construct :: Fun (Elems v) v) a b c d e



----------------------------------------------------------------
-- Helpers
----------------------------------------------------------------

-- | Generalize 'const' function. This type class is total and have
--   instances for all possible types. It's however is impossible to
--   express so @ConstF@ constraint will pop up from time to time.
class ConstF (xs :: [*]) where
  constF :: a -> Fun xs a

instance ConstF '[] where
  constF = Fun
instance ConstF xs => ConstF (x ': xs) where
  constF (a :: a) = Fun $ \_ -> unFun (constF a :: Fun xs a)



----------------------------------------------------------------
-- * Instances
----------------------------------------------------------------

-- | Unit is empty heterogeneous vector
instance HVector () where
  type Elems () = '[]
  construct = Fun ()
  inspect () (Fun f) = f



instance HVector (a,b) where
  type Elems (a,b) = '[a,b]
  construct = Fun (,)
  inspect (a,b) (Fun f) = f a b
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c) where
  type Elems (a,b,c) = '[a,b,c]
  construct = Fun (,,)
  inspect (a,b,c) (Fun f) = f a b c
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d) where
  type Elems (a,b,c,d) = '[a,b,c,d]
  construct = Fun (,,,)
  inspect (a,b,c,d) (Fun f) = f a b c d
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e) where
  type Elems (a,b,c,d,e) = '[a,b,c,d,e]
  construct = Fun (,,,,)
  inspect (a,b,c,d,e) (Fun f) = f a b c d e
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f) where
  type Elems (a,b,c,d,e,f) = '[a,b,c,d,e,f]
  construct = Fun (,,,,,)
  inspect (a,b,c,d,e,f) (Fun fun) = fun a b c d e f
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g) where
  type Elems (a,b,c,d,e,f,g) = '[a,b,c,d,e,f,g]
  construct = Fun (,,,,,,)
  inspect (a,b,c,d,e,f,g) (Fun fun) = fun a b c d e f g
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}


----------------------------------------------------------------
-- Generic HVec
----------------------------------------------------------------

-- | Generic heterogeneous vector
newtype HVec (xs :: [*]) = HVec (Array Any)

instance (HVecClass xs, ListLen xs, Functor (Fun xs)) => HVector (HVec xs) where
  type Elems (HVec xs) = xs
  inspect (HVec arr) f = inspectWorker arr 0 f
  construct = fmap fini (constructWorker 0)
    where
      size = listLen (Proxy :: Proxy xs)
      fini = HVec . runBox size
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

-- Implementation of heterogeneous vector
class HVecClass xs where
  inspectWorker :: Array Any -> Int -> Fun xs r -> r
  constructWorker :: Int -- ^ Offset
                  -> Fun xs (Box Any)


instance HVecClass '[] where
  inspectWorker   _ _ = unFun
  constructWorker _   = Fun $ Box (const $ return ())
  {-# INLINE inspectWorker #-}
  {-# INLINE constructWorker #-}


instance (Functor (Fun xs), HVecClass xs) => HVecClass (x ': xs) where
  inspectWorker arr i (Fun f :: Fun (x ': xs) r)
    = inspectWorker arr (i+1) (Fun (f x) :: Fun xs r)
    where
      x = unsafeCoerce $ indexArray arr i
  --
  constructWorker off = Fun $ \a ->
    unFun (writeToBox (unsafeCoerce a) off `fmap` step)
    where
      step = constructWorker (off + 1) :: Fun xs (Box Any)
  {-# INLINE inspectWorker #-}
  {-# INLINE constructWorker #-}




-- Helper data type
newtype Box a = Box (forall s. MutableArray s a -> ST s ())

writeToBox :: a -> Int -> Box a -> Box a
writeToBox a i (Box f) = Box $ \arr -> f arr >> writeArray arr i a
{-# INLINE writeToBox #-}

runBox :: Int -> Box a -> Array a
runBox size (Box f) = runST $ do arr <- newArray size uninitialised
                                 f arr
                                 unsafeFreezeArray arr
{-# INLINE runBox #-}


uninitialised :: a
uninitialised = error "Data.Vector.HFixed: uninitialised element"
