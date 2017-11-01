{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE ExplicitNamespaces    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module Data.Vector.HFixed.Class (
    -- * Types and type classes
    -- ** Peano numbers
    S
  , Z
    -- * Isomorphism between Peano numbers and Nats
  , NatIso
  , ToPeano
  , ToNat
    -- ** N-ary functions
  , Fn
  , Fun
  , TFun(..)
    -- ** Type functions
  , Proxy(..)
  , type (++)()
  , Len
  , Wrap
  , HomList
    -- ** Type classes
  , Arity(..)
  , ArityC(..)
  , HVector(..)
  , HVectorF(..)
    -- *** Witnesses
  , WitWrapped(..)
  , WitWrapIndex(..)
  , WitAllInstances(..)
    -- ** CPS-encoded vector
  , ContVec(..)
  , ContVecF(..)
  -- , toContVec
  -- , toContVecF
  , cons
  , consF
    -- ** Interop with homogeneous vectors
  -- , HomArity(..)
  -- , homInspect
  -- , homConstruct
    -- * Operations of Fun
    -- ** Primitives for Fun
  , curryFun
  , uncurryFun
  , uncurryMany
  , curryMany
  , constFun
  , stepFun
    -- ** Primitives for TFun
  , constTFun
  , curryTFun
  , uncurryTFun
  , shuffleTF
  , stepTFun
    -- ** More complicated functions
  , concatF
  , shuffleF
  , lensWorkerF
  , lensWorkerTF
  , Index(..)
  ) where

import Control.Applicative   (Applicative(..),(<$>))
import Data.Coerce
import Data.Complex          (Complex(..))
import Data.Typeable         (Proxy(..))
import Data.Functor.Identity (Identity(..))

import           Data.Vector.Fixed.Cont   (S,Z)
import           Data.Vector.Fixed.Cont   (ToPeano,ToNat,NatIso)
import qualified Data.Vector.Fixed                as F
import qualified Data.Vector.Fixed.Cont           as F (curryFirst)
import qualified Data.Vector.Fixed.Unboxed        as U
import qualified Data.Vector.Fixed.Primitive      as P
import qualified Data.Vector.Fixed.Storable       as S
import qualified Data.Vector.Fixed.Boxed          as B

import Unsafe.Coerce (unsafeCoerce)
import GHC.Generics hiding (S)

import Data.Vector.HFixed.TypeFuns



----------------------------------------------------------------
-- Types
----------------------------------------------------------------

-- | Type family for N-ary function. Types of function parameters are
--   encoded as the list of types.
type family Fn (f :: * -> *) (as :: [*]) b where
  Fn f '[]      b = b
  Fn f (a : as) b = f a -> Fn f as b

-- | Newtype wrapper for function where all type parameters have same
--   type constructor. This type is required for writing function
--   which works with monads, appicatives etc.
newtype TFun f as b = TFun { unTFun :: Fn f as b }

-- | Newtype wrapper to work around of type families' lack of
--   injectivity.
type Fun = TFun Identity



----------------------------------------------------------------
-- Generic operations
----------------------------------------------------------------

-- | Type class for dealing with N-ary function in generic way. Both
--   'accum' and 'apply' work with accumulator data types which are
--   polymorphic. So it's only possible to write functions which
--   rearrange elements in vector using plain ADT. It's possible to
--   get around it by using GADT as accumulator (See 'ArityC' and
--   function which use it)
--
--   This is also somewhat a kitchen sink module. It contains
--   witnesses which could be used to prove type equalities or to
--   bring instance in scope.
class F.Arity (Len xs) => Arity (xs :: [*]) where
  -- | Fold over /N/ elements exposed as N-ary function.
  accum :: (forall a as. t (a : as) -> f a -> t as)
        -- ^ Step function. Applies element to accumulator.
        -> (t '[] -> b)
        -- ^ Extract value from accumulator.
        -> t xs
        -- ^ Initial state.
        -> TFun f xs b

  -- | Apply values to N-ary function
  apply :: (forall a as. t (a : as) -> (f a, t as))
        -- ^ Extract value to be applied to function.
        -> t xs
        -- ^ Initial state.
        -> ContVecF xs f

  -- | Size of type list as integer.
  arity :: p xs -> Int

  witWrapped   :: WitWrapped f xs


-- | Declares that every type in list satisfy constraint @c@
class Arity xs => ArityC c xs where
  witAllInstances :: WitAllInstances c xs

instance ArityC c '[] where
  witAllInstances = WitAllInstancesNil
  {-# INLINE witAllInstances #-}
instance (c x, ArityC c xs) => ArityC c (x : xs) where
  witAllInstances = WitAllInstancesCons (witAllInstances :: WitAllInstances c xs)
  {-# INLINE witAllInstances #-}


-- | Witness that observe fact that if we have instance @Arity xs@
--   than we have instance @Arity (Wrap f xs)@.
data WitWrapped f xs where
  WitWrapped :: Arity (Wrap f xs) => WitWrapped f xs

-- | Witness that all elements of type list satisfy predicate @c@.
data WitAllInstances c xs where
  WitAllInstancesNil  :: WitAllInstances c '[]
  WitAllInstancesCons :: c x => WitAllInstances c xs -> WitAllInstances c (x : xs)


instance Arity '[] where
  accum _ f t = TFun (f t)
  apply _ _   = ContVecF unTFun
  {-# INLINE accum #-}
  {-# INLINE apply #-}
  arity _     = 0
  {-# INLINE arity #-}

  witWrapped   = WitWrapped
  {-# INLINE witWrapped #-}

instance Arity xs => Arity (x : xs) where
  accum f g t = uncurryTFun (\a -> accum f g (f t a))
  apply f t   = case f t of (a,u) -> consF a (apply f u)
  {-# INLINE accum #-}
  {-# INLINE apply #-}
  arity _     = 1 + arity (Proxy :: Proxy xs)
  {-# INLINE arity        #-}

  witWrapped :: forall f. WitWrapped f (x : xs)
  witWrapped = case witWrapped :: WitWrapped f xs of
                 WitWrapped -> WitWrapped
  {-# INLINE witWrapped #-}



-- | Type class for heterogeneous vectors. Instance should specify way
-- to construct and deconstruct itself
--
-- Note that this type class is extremely generic. Almost any single
-- constructor data type could be made instance. It could be
-- monomorphic, it could be polymorphic in some or all fields it
-- doesn't matter. Only law instance should obey is:
--
-- > inspect v construct = v
--
-- Default implementation which uses 'Generic' is provided.
class Arity (Elems v) => HVector v where
  type Elems v :: [*]
  type Elems v = GElems (Rep v)
  -- | Function for constructing vector
  construct :: Fun (Elems v) v
  default construct :: (Generic v, GHVector (Rep v), GElems (Rep v) ~ Elems v)
                    => Fun (Elems v) v
  construct = fmap to gconstruct
  -- | Function for deconstruction of vector. It applies vector's
  --   elements to N-ary function.
  inspect :: v -> Fun (Elems v) a -> a
  default inspect :: (Generic v, GHVector (Rep v), GElems (Rep v) ~ Elems v)
                  => v -> Fun (Elems v) a -> a
  inspect v = ginspect (from v)
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}


-- | Type class for partially homogeneous vector where every element
--   in the vector have same type constructor. Vector itself is
--   parametrized by that constructor
class Arity (ElemsF v) => HVectorF (v :: (* -> *) -> *) where
  -- | Elements of the vector without type constructors
  type ElemsF v :: [*]
  inspectF   :: v f -> TFun f (ElemsF v) a -> a
  constructF :: TFun f (ElemsF v) (v f)



----------------------------------------------------------------
-- Interop with homogeneous vectors
----------------------------------------------------------------
{-
-- | Conversion between homogeneous and heterogeneous N-ary functions.
class (F.Arity n, Arity (HomList n a)) => HomArity n a where
  -- | Convert n-ary homogeneous function to heterogeneous.
  toHeterogeneous :: F.Fun n a r -> Fun (HomList n a) r
  -- | Convert heterogeneous n-ary function to homogeneous.
  toHomogeneous   :: Fun (HomList n a) r -> F.Fun n a r


instance HomArity Z a where
  toHeterogeneous = Fun   . F.unFun
  toHomogeneous   = F.Fun . unFun
  {-# INLINE toHeterogeneous #-}
  {-# INLINE toHomogeneous   #-}

instance HomArity n a => HomArity (S n) a where
  toHeterogeneous f
    = Fun $ \a -> unFun $ toHeterogeneous (F.curryFirst f a)
  toHomogeneous (f :: Fun (a : HomList n a) r)
    = F.Fun $ \a -> F.unFun (toHomogeneous $ curryFun f a :: F.Fun n a r)
  {-# INLINE toHeterogeneous #-}
  {-# INLINE toHomogeneous   #-}

-- | Default implementation of 'inspect' for homogeneous vector.
homInspect :: (F.Vector v a, HomArity (F.Dim v) a)
           => v a -> Fun (HomList (F.Dim v) a) r -> r
homInspect v f = F.inspect v (toHomogeneous f)
{-# INLINE homInspect #-}

-- | Default implementation of 'construct' for homogeneous vector.
homConstruct :: forall v a.
                (F.Vector v a, HomArity (F.Dim v) a)
             => Fun (HomList (F.Dim v) a) (v a)
homConstruct = toHeterogeneous (F.construct :: F.Fun (F.Dim v) a (v a))
{-# INLINE homConstruct #-}



instance HomArity n a => HVector (B.Vec n a) where
  type Elems (B.Vec n a) = HomList n a
  inspect   = homInspect
  construct = homConstruct
  {-# INLINE inspect   #-}
  {-# INLINE construct #-}

instance (U.Unbox n a, HomArity n a) => HVector (U.Vec n a) where
  type Elems (U.Vec n a) = HomList n a
  inspect   = homInspect
  construct = homConstruct
  {-# INLINE inspect   #-}
  {-# INLINE construct #-}

instance (S.Storable a, HomArity n a) => HVector (S.Vec n a) where
  type Elems (S.Vec n a) = HomList n a
  inspect   = homInspect
  construct = homConstruct
  {-# INLINE inspect   #-}
  {-# INLINE construct #-}

instance (P.Prim a, HomArity n a) => HVector (P.Vec n a) where
  type Elems (P.Vec n a) = HomList n a
  inspect   = homInspect
  construct = homConstruct
  {-# INLINE inspect   #-}
  {-# INLINE construct #-}
-}

----------------------------------------------------------------
-- CPS-encoded vectors
----------------------------------------------------------------

-- 
-- newtype ContVec xs = ContVec { runContVec :: forall r. Fun xs r -> r }

instance Arity xs => HVector (ContVecF xs Identity) where
  type Elems (ContVecF xs Identity) = xs
  construct = accum
    (\(T_mkN f) (Identity x) -> T_mkN (f . cons x))
    (\(T_mkN f)              -> f (ContVecF unTFun))
    (T_mkN id)
  inspect (ContVecF cont) f = cont f
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

newtype T_mkN all xs = T_mkN (ContVec xs -> ContVec all)

-- | CPS-encoded heterogeneous vector.
type ContVec xs = ContVecF xs Identity

-- | CPS-encoded partially heterogeneous vector.
newtype ContVecF xs f = ContVecF { runContVecF :: forall r. TFun f xs r -> r }

instance Arity xs => HVectorF (ContVecF xs) where
  type ElemsF (ContVecF xs) = xs
  inspectF (ContVecF cont) = cont
  constructF = constructFF
  {-# INLINE constructF #-}
  {-# INLINE inspectF   #-}

constructFF :: forall f xs. (Arity xs) => TFun f xs (ContVecF xs f)
{-# INLINE constructFF #-}
constructFF = accum (\(TF_mkN f) x -> TF_mkN (f . consF x))
                    (\(TF_mkN f)   -> f $ ContVecF unTFun)
                    (TF_mkN id)

newtype TF_mkN f all xs = TF_mkN (ContVecF xs f -> ContVecF all f)


-- | Cons element to the vector
cons :: x -> ContVec xs -> ContVec (x : xs)
cons x (ContVecF cont) = ContVecF $ \f -> cont $ curryFun f x
{-# INLINE cons #-}

-- | Cons element to the vector
consF :: f x -> ContVecF xs f -> ContVecF (x : xs) f
consF x (ContVecF cont) = ContVecF $ \f -> cont $ curryTFun f x
{-# INLINE consF #-}



----------------------------------------------------------------
-- Instances of Fun
----------------------------------------------------------------

instance (Arity xs) => Functor (TFun f xs) where
  fmap f (TFun g0)
    = accum (\(TF_fmap g) a -> TF_fmap (g a))
            (\(TF_fmap r)   -> f r)
            (TF_fmap g0)
  {-# INLINE fmap #-}

instance (Arity xs) => Applicative (TFun f xs) where
  pure r = accum (\Proxy _ -> Proxy)
                 (\Proxy   -> r)
                 (Proxy)
  {-# INLINE pure  #-}
  (TFun f0 :: TFun f xs (a -> b)) <*> (TFun g0 :: TFun f xs a)
    = accum (\(TF_ap f g) a -> TF_ap (f a) (g a))
            (\(TF_ap f g)   -> f g)
            ( TF_ap f0 g0 :: TF_ap f (a -> b) a xs)
  {-# INLINE (<*>) #-}

instance Arity xs => Monad (TFun f xs) where
  return  = pure
  f >>= g = shuffleTF g <*> f
  {-# INLINE return #-}
  {-# INLINE (>>=)  #-}

newtype TF_fmap f a   xs = TF_fmap (Fn f xs a)
data    TF_ap   f a b xs = TF_ap   (Fn f xs a) (Fn f xs b)



----------------------------------------------------------------
-- Operations on Fun
----------------------------------------------------------------

-- | Apply single parameter to function
curryFun :: Fun (x : xs) r -> x -> Fun xs r
curryFun = coerce
{-# INLINE curryFun #-}

-- | Uncurry N-ary function.
uncurryFun :: (x -> Fun xs r) -> Fun (x : xs) r
uncurryFun = coerce
{-# INLINE uncurryFun #-}

-- | Conversion function
uncurryMany :: forall xs ys r. Arity xs => Fun xs (Fun ys r) -> Fun (xs ++ ys) r
-- NOTE: GHC is not smart enough to figure out that:
--
--       > Fn xs (Fn ys) r ~ Fn (xs ++ ys) r
--
--       It's possible to construct type safe definition but it's
--       quite complicated and increase compile time and may hurrt
--       performance
{-# INLINE uncurryMany #-}
uncurryMany = unsafeCoerce

-- | Curry first /n/ arguments of N-ary function.
curryMany :: forall xs ys r. Arity xs => Fun (xs ++ ys) r -> Fun xs (Fun ys r)
-- NOTE: See uncurryMany
{-# INLINE curryMany #-}
curryMany = unsafeCoerce


-- | Add one parameter to function which is ignored.
constFun :: Fun xs r -> Fun (x : xs) r
constFun = uncurryFun . const
{-# INLINE constFun #-}

-- | Add one parameter to function which is ignored.
constTFun :: TFun f xs r -> TFun f (x : xs) r
constTFun = uncurryTFun . const
{-# INLINE constTFun #-}

-- | Transform function but leave outermost parameter untouched.
stepFun :: (Fun xs a -> Fun ys b) -> Fun (x : xs) a -> Fun (x : ys) b
stepFun g = uncurryFun . fmap g . curryFun
{-# INLINE stepFun #-}

-- | Transform function but leave outermost parameter untouched.
stepTFun :: (TFun f xs a       -> TFun f ys b)
         -> (TFun f (x : xs) a -> TFun f (x : ys) b)
stepTFun g = uncurryTFun . fmap g . curryTFun
{-# INLINE stepTFun #-}

-- | Concatenate n-ary functions. This function combine results of
--   both N-ary functions and merge their parameters into single list.
concatF :: (Arity xs, Arity ys)
        => (a -> b -> c) -> Fun xs a -> Fun ys b -> Fun (xs ++ ys) c
{-# INLINE concatF #-}
concatF f funA funB = uncurryMany $ fmap go funA
  where
    go a = fmap (\b -> f a b) funB

-- | Move first argument of function to its result. This function is
--   useful for implementation of lens.
shuffleF :: forall x xs r. Arity xs => (x -> Fun xs r) -> Fun xs (x -> r)
{-# INLINE shuffleF #-}
shuffleF = undefined
-- shuffleF fun = accum
--   (\(T_shuffle f) a -> T_shuffle (\x -> f x a))
--   (\(T_shuffle f)   -> f)
--   (T_shuffle (fmap unFun fun))

-- data T_shuffle x r xs = T_shuffle (Fn (x : xs) r)

-- | Helper for lens implementation.
lensWorkerF :: forall f r x y xs. (Functor f, Arity xs)
            => (x -> f y) -> Fun (y : xs) r -> Fun (x : xs) (f r)
{-# INLINE lensWorkerF #-}
lensWorkerF g f
  = uncurryFun
  $ \x -> (\r -> fmap (r $) (g x)) <$> shuffleF (curryFun f)

-- | Helper for lens implementation.
lensWorkerTF :: forall f g r x y xs. (Functor f, Arity xs)
             => (g x -> f (g y))
             -> TFun g (y : xs) r
             -> TFun g (x : xs) (f r)
{-# INLINE lensWorkerTF #-}
lensWorkerTF g f
  = uncurryTFun
  $ \x -> (\r -> fmap (r $) (g x)) <$> shuffleTF (curryTFun f)


----------------------------------------------------------------
-- Operations on TFun
----------------------------------------------------------------

-- | Apply single parameter to function
curryTFun :: TFun f (x : xs) r -> f x -> TFun f xs r
curryTFun = coerce
{-# INLINE curryTFun #-}

-- | Uncurry single parameter
uncurryTFun :: (f x -> TFun f xs r) -> TFun f (x : xs) r
uncurryTFun = coerce
{-# INLINE uncurryTFun #-}

-- | Move first argument of function to its result. This function is
--   useful for implementation of lens.
shuffleTF :: forall f x xs r. Arity xs
          => (x -> TFun f xs r) -> TFun f xs (x -> r)
{-# INLINE shuffleTF #-}
shuffleTF fun0 = accum
  (\(TF_shuffle f) a -> TF_shuffle (\x -> f x a))
  (\(TF_shuffle f)   -> f)
  (TF_shuffle (fmap unTFun fun0))

data TF_shuffle f x r xs = TF_shuffle (x -> Fn f xs r)



----------------------------------------------------------------
-- Indexing
----------------------------------------------------------------

-- | Indexing of vectors
class F.Arity n => Index (n :: *) (xs :: [*]) where
  -- | Type at position n
  type ValueAt n xs :: *
  -- | List of types with n'th element replaced by /a/.
  type NewElems n xs a :: [*]
  -- | Getter function for vectors
  getF :: n -> Fun xs (ValueAt n xs)
  -- | Putter function. It applies value @x@ to @n@th parameter of
  --   function.
  putF :: n -> ValueAt n xs -> Fun xs r -> Fun xs r
  -- | Helper for implementation of lens
  lensF :: (Functor f, v ~ ValueAt n xs)
        => n -> (v -> f v) -> Fun xs r -> Fun xs (f r)
  -- | Helper for type-changing lens
  lensChF :: (Functor f)
          => n -> (ValueAt n xs -> f a) -> Fun (NewElems n xs a) r -> Fun xs (f r)
  witWrapIndex :: WitWrapIndex f n xs


-- | Proofs for the indexing of wrapped type lists.
data WitWrapIndex f n xs where
  WitWrapIndex :: ( ValueAt n (Wrap f xs) ~ f (ValueAt n xs)
                  , Index n (Wrap f xs)
                  , Arity (Wrap f xs)
                  ) => WitWrapIndex f n xs


instance Arity xs => Index Z (x : xs) where
  type ValueAt  Z (x : xs)   = x
  type NewElems Z (x : xs) a = a : xs
  getF  _     = undefined -- Fun $ \x -> unFun (pure x :: Fun xs x)
  putF  _ x f = constFun $ curryFun f x
  lensF   _     = lensWorkerF
  lensChF _     = lensWorkerF
  {-# INLINE getF    #-}
  {-# INLINE putF    #-}
  {-# INLINE lensF   #-}
  {-# INLINE lensChF #-}
  witWrapIndex :: forall f. WitWrapIndex f Z (x : xs)
  witWrapIndex = case witWrapped :: WitWrapped f xs of
                   WitWrapped -> WitWrapIndex
  {-# INLINE witWrapIndex #-}

instance Index n xs => Index (S n) (x : xs) where
  type ValueAt  (S n) (x : xs)   = ValueAt n xs
  type NewElems (S n) (x : xs) a = x : NewElems n xs a
  getF    _   = constFun $ getF    (undefined :: n)
  putF    _ x = stepFun  $ putF    (undefined :: n) x
  lensF   _ f = stepFun  $ lensF   (undefined :: n) f
  lensChF _ f = stepFun  $ lensChF (undefined :: n) f
  {-# INLINE getF    #-}
  {-# INLINE putF    #-}
  {-# INLINE lensF   #-}
  {-# INLINE lensChF #-}
  witWrapIndex :: forall f. WitWrapIndex f (S n) (x : xs)
  witWrapIndex = case witWrapIndex :: WitWrapIndex f n xs of
                   WitWrapIndex -> WitWrapIndex
  {-# INLINE witWrapIndex #-}



----------------------------------------------------------------
-- Instances
----------------------------------------------------------------
{-
-- | Unit is empty heterogeneous vector
instance HVector () where
  type Elems () = '[]
  construct = Fun ()
  inspect () (Fun f) = f

instance HVector (Complex a) where
  type Elems (Complex a) = '[a,a]
  construct = Fun (:+)
  inspect (r :+ i) (Fun f) = f r i
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

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

instance HVector (a,b,c,d,e,f,g,h) where
  type Elems (a,b,c,d,e,f,g,h) = '[a,b,c,d,e,f,g,h]
  construct = Fun (,,,,,,,)
  inspect (a,b,c,d,e,f,g,h) (Fun fun) = fun a b c d e f g h
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i) where
  type Elems (a,b,c,d,e,f,g,h,i) = '[a,b,c,d,e,f,g,h,i]
  construct = Fun (,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i) (Fun fun) = fun a b c d e f g h i
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j) where
  type Elems (a,b,c,d,e,f,g,h,i,j) = '[a,b,c,d,e,f,g,h,i,j]
  construct = Fun (,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j) (Fun fun) = fun a b c d e f g h i j
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k) = '[a,b,c,d,e,f,g,h,i,j,k]
  construct = Fun (,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k) (Fun fun) = fun a b c d e f g h i j k
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l) = '[a,b,c,d,e,f,g,h,i,j,k,l]
  construct = Fun (,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l) (Fun fun) = fun a b c d e f g h i j k l
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m) = '[a,b,c,d,e,f,g,h,i,j,k,l,m]
  construct = Fun (,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m) (Fun fun) = fun a b c d e f g h i j k l m
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n) = '[a,b,c,d,e,f,g,h,i,j,k,l,m,n]
  construct = Fun (,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n) (Fun fun) =
    fun a b c d e f g h i j k l m n
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o]
  construct = Fun (,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) (Fun fun) =
    fun a b c d e f g h i j k l m n o
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p) =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p]
  construct = Fun (,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p) (Fun fun) =
    fun a b c d e f g h i j k l m n o p
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q) =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q]
  construct = Fun (,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q) (Fun fun) =
    fun a b c d e f g h i j k l m n o p q
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r) =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r]
  construct = Fun (,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r) (Fun fun) =
    fun a b c d e f g h i j k l m n o p q r
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s) =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s]
  construct = Fun (,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s) (Fun fun) =
    fun a b c d e f g h i j k l m n o p q r s
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t) =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t]
  construct = Fun (,,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t) (Fun fun) =
    fun a b c d e f g h i j k l m n o p q r s t
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u) =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u]
  construct = Fun (,,,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u) (Fun fun) =
    fun a b c d e f g h i j k l m n o p q r s t u
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v) =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v]
  construct = Fun (,,,,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v) (Fun fun) =
    fun a b c d e f g h i j k l m n o p q r s t u v
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w) =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w]
  construct = Fun (,,,,,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w) (Fun fun) =
    fun a b c d e f g h i j k l m n o p q r s t u v w
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x) =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x]
  construct = Fun (,,,,,,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x) (Fun fun) =
    fun a b c d e f g h i j k l m n o p q r s t u v w x
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y) =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y]
  construct = Fun (,,,,,,,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y) (Fun fun) =
    fun a b c d e f g h i j k l m n o p q r s t u v w x y
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}


instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z) where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z) =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z]
  construct = Fun (,,,,,,,,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z) (Fun fun) =
    fun a b c d e f g h i j k l m n o p q r s t u v w x y z
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}


instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a') where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a') =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a']
  construct = Fun (,,,,,,,,,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a') (Fun fun) =
    fun a b c d e f g h i j k l m n o p q r s t u v w x y z a'
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b') where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b') =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b']
  construct = Fun (,,,,,,,,,,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b') (Fun fun) = fun a b c d e f g h i j k l m n o p q r s t u v w x y z a' b'
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c') where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c') =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c']
  construct = Fun (,,,,,,,,,,,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c') (Fun fun) = fun a b c d e f g h i j k l m n o p q r s t u v w x y z a' b' c'
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c',d') where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c',d') =
    '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c',d']
  construct = Fun (,,,,,,,,,,,,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c',d') (Fun fun) = fun a b c d e f g h i j k l m n o p q r s t u v w x y z a' b' c' d'
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c',d',e') where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c',d',e') = '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c',d',e']
  construct = Fun (,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c',d',e') (Fun fun) =
    fun a b c d e f g h i j k l m n o p q r s t u v w x y z a' b' c' d' e'
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c',d',e',f') where
  type Elems (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c',d',e',f') = '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c',d',e',f']
  construct = Fun (,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,)
  inspect (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,a',b',c',d',e',f') (Fun fun) =
    fun a b c d e f g h i j k l m n o p q r s t u v w x y z a' b' c' d' e' f'
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}
-}

----------------------------------------------------------------
-- Generics
----------------------------------------------------------------

class GHVector (v :: * -> *) where
  type GElems v :: [*]
  gconstruct :: Fun (GElems v) (v p)
  ginspect   :: v p -> Fun (GElems v) r -> r


-- We simply skip metadata
instance (GHVector f, Arity (GElems f)) => GHVector (M1 i c f) where
  type GElems (M1 i c f) = GElems f
  gconstruct = fmap M1 gconstruct
  ginspect v = ginspect (unM1 v)
  {-# INLINE gconstruct #-}
  {-# INLINE ginspect   #-}


instance ( GHVector f, GHVector g, Arity (GElems f), Arity (GElems g)
         ) => GHVector (f :*: g) where
  type GElems (f :*: g) = GElems f ++ GElems g

  gconstruct = concatF (:*:) gconstruct gconstruct
  ginspect (f :*: g) fun
    = ginspect g $ ginspect f $ curryMany fun
  {-# INLINE gconstruct #-}
  {-# INLINE ginspect   #-}


-- Recursion is terminated by simple field
instance GHVector (K1 R x) where
  type GElems (K1 R x) = '[x]
  gconstruct               = TFun (K1 . runIdentity)
  ginspect (K1 x) (TFun f) = f (Identity x) -- f (Identity x)
  {-# INLINE gconstruct #-}
  {-# INLINE ginspect   #-}


-- Unit types are empty vectors
instance GHVector U1 where
  type GElems U1 = '[]
  gconstruct          = coerce U1
  ginspect _ (TFun f) = f
  {-# INLINE gconstruct #-}
  {-# INLINE ginspect   #-}
