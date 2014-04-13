{-# LANGUAGE CPP                   #-}
{-# LANGUAGE GADTs                 #-}
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
{-# LANGUAGE InstanceSigs #-}
module Data.Vector.HFixed.Class (
    -- * Types and type classes
    -- ** Peano numbers
    S
  , Z
#if __GLASGOW_HASKELL__ >= 708
    -- * Isomorphism between Peano numbers and Nats
  , NatIso
  , ToPeano
  , ToNat
#endif
    -- ** N-ary functions
  , Fn
  , Fun(..)
  , TFun(..)
  , funToTFun
  , tfunToFun
    -- ** Type functions
  , Proxy(..)
  , (++)()
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
  , WitConcat(..)
  , WitNestedFun(..)
  , WitLenWrap(..)
  , WitWrapIndex(..)
  , WitAllInstances(..)
    -- ** CPS-encoded vector
  , ContVec(..)
  , ContVecF(..)
  , toContVec
  , toContVecF
  , cons
  , consF
    -- ** Interop with homogeneous vectors
  , HomArity(..)
  , homInspect
  , homConstruct
    -- * Operations of Fun
    -- ** Primitives for Fun
  , curryFun
  , uncurryFun
  , uncurryFun2
  , curryMany
  , constFun
  , stepFun
    -- ** Primitives for TFun
  , curryTFun
  , uncurryTFun
  , uncurryTFun2
  , shuffleTF
    -- ** More complicated functions
  , concatF
  , shuffleF
  , lensWorkerF
  , Index(..)
  ) where

import Control.Applicative (Applicative(..),(<$>))
import Data.Complex        (Complex(..))

import           Data.Vector.Fixed.Cont   (S,Z)
#if __GLASGOW_HASKELL__ >= 708
import           Data.Vector.Fixed.Cont   (ToPeano,ToNat,NatIso)
#endif
import qualified Data.Vector.Fixed                as F
import qualified Data.Vector.Fixed.Cont           as F (apFun)
import qualified Data.Vector.Fixed.Unboxed        as U
import qualified Data.Vector.Fixed.Primitive      as P
import qualified Data.Vector.Fixed.Storable       as S
import qualified Data.Vector.Fixed.Boxed          as B

import GHC.Generics hiding (Arity(..),S)
import GHC.Exts     (coerce)

import Data.Vector.HFixed.TypeFuns



----------------------------------------------------------------
-- Types
----------------------------------------------------------------

-- | Type family for N-ary function. Types of function parameters are
--   encoded as the list of types.
type family   Fn (as :: [*]) b
type instance Fn '[]       b = b
type instance Fn (a ': as) b = a -> Fn as b

-- | Newtype wrapper to work around of type families' lack of
--   injectivity.
newtype Fun (as :: [*]) b = Fun { unFun :: Fn as b }

-- | Newtype wrapper for function where all type parameters have same
--   type constructor. This type is required for writing function
--   which works with monads, appicatives etc.
newtype TFun f as b = TFun { unTFun :: Fn (Wrap f as) b }

-- | Cast /Fun/ to equivalent /TFun/
funToTFun  :: Fun (Wrap f xs) b -> TFun f xs b
funToTFun = coerce
{-# INLINE funToTFun #-}

-- | Cast /TFun/ to equivalent /Fun/
tfunToFun :: TFun f xs b -> Fun (Wrap f xs) b
tfunToFun = coerce
{-# INLINE tfunToFun #-}



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
  accum :: (forall a as. t (a ': as) -> a -> t as)
           -- ^ Step function. Applies element to accumulator.
        -> (t '[] -> b)
           -- ^ Extract value from accumulator.
        -> t xs
           -- ^ Initial state.
        -> Fn xs b

  -- | Apply values to N-ary function
  apply :: (forall a as. t (a ': as) -> (a, t as))
           -- ^ Extract value to be applied to function.
        -> t xs
           -- ^ Initial state.
        -> ContVec xs
  -- | Apply value to N-ary function using monadic actions
  applyM :: Monad m
         => (forall a as. t (a ': as) -> m (a, t as))
            -- ^ Extract value to be applied to function
         -> t xs
            -- ^ Initial state
         -> m (ContVec xs)

  -- | Analog of accum
  accumTy :: (forall a as. t (a ': as) -> f a -> t as)
          -> (t '[] -> b)
          -> t xs
          -> Fn (Wrap f xs) b

  -- | Analog of 'apply' which allows to works with vectors which
  --   elements are wrapped in the newtype constructor.
  applyTy :: (forall a as. t (a ': as) -> (f a, t as))
          -> t xs
          -> Fn (Wrap f xs) b
          -> b

  -- | Size of type list as integer.
  arity :: p xs -> Int

  witWrapped   :: WitWrapped f xs
  witConcat    :: Arity ys => WitConcat xs ys
  witNestedFun :: WitNestedFun xs ys r
  witLenWrap   :: WitLenWrap f xs


-- | Declares that every type in list satisfy constraint @c@
class Arity xs => ArityC c xs where
  witAllInstances :: WitAllInstances c xs

instance ArityC c '[] where
  witAllInstances = WitAllInstancesNil
  {-# INLINE witAllInstances #-}
instance (c x, ArityC c xs) => ArityC c (x ': xs) where
  witAllInstances = WitAllInstancesCons (witAllInstances :: WitAllInstances c xs)
  {-# INLINE witAllInstances #-}


-- | Witness that observe fact that if we have instance @Arity xs@
--   than we have instance @Arity (Wrap f xs)@.
data WitWrapped f xs where
  WitWrapped :: Arity (Wrap f xs) => WitWrapped f xs

-- | Witness that observe fact that @(Arity xs, Arity ys)@ implies
--   @Arity (xs++ys)@
data WitConcat xs ys where
  WitConcat :: (Arity (xs++ys)) => WitConcat xs ys

-- | Observes fact that @Fn (xs++ys) r ~ Fn xs (Fn ys r)@
data WitNestedFun xs ys r where
  WitNestedFun :: (Fn (xs++ys) r ~ Fn xs (Fn ys r)) => WitNestedFun xs ys r

-- | Observe fact than @Len xs ~ Len (Wrap f xs)@
data WitLenWrap f xs where
  WitLenWrap :: Len xs ~ Len (Wrap f xs) => WitLenWrap f xs

-- | Witness that all elements of type list satisfy predicate @c@.
data WitAllInstances c xs where
  WitAllInstancesNil  :: WitAllInstances c '[]
  WitAllInstancesCons :: c x => WitAllInstances c xs -> WitAllInstances c (x ': xs)


instance Arity '[] where
  accum   _ f t = f t
  apply   _ _   = ContVec unFun
  applyM  _ _   = return (ContVec unFun)
  accumTy _ f t = f t
  applyTy _ _ b = b
  {-# INLINE accum   #-}
  {-# INLINE apply   #-}
  {-# INLINE applyM  #-}
  {-# INLINE accumTy #-}
  {-# INLINE applyTy #-}
  arity _     = 0
  {-# INLINE arity #-}

  witWrapped   = WitWrapped
  witConcat    = WitConcat
  witNestedFun = WitNestedFun
  witLenWrap   = WitLenWrap
  {-# INLINE witWrapped #-}
  {-# INLINE witConcat #-}
  {-# INLINE witNestedFun #-}
  {-# INLINE witLenWrap #-}

instance Arity xs => Arity (x ': xs) where
  accum   f g t = \a -> accum f g (f t a)
  apply   f t   = case f t of (a,u) -> cons a (apply f u)
  applyM  f t   = do (a,t') <- f t
                     vec    <- applyM f t'
                     return $ cons a vec
  accumTy f g t = \a -> accumTy f g (f t a)
  applyTy f t h = case f t of (a,u) -> applyTy f u (h a)
  {-# INLINE accum   #-}
  {-# INLINE apply   #-}
  {-# INLINE applyM  #-}
  {-# INLINE accumTy #-}
  {-# INLINE applyTy #-}
  arity _     = 1 + arity (Proxy :: Proxy xs)
  {-# INLINE arity        #-}

  witWrapped :: forall f. WitWrapped f (x ': xs)
  witWrapped = case witWrapped :: WitWrapped f xs of
                 WitWrapped -> WitWrapped
  {-# INLINE witWrapped #-}
  witConcat :: forall ys. Arity ys => WitConcat (x ': xs) ys
  witConcat = case witConcat :: WitConcat xs ys of
                WitConcat -> WitConcat
  {-# INLINE witConcat  #-}
  witNestedFun :: forall ys r. WitNestedFun (x ': xs) ys r
  witNestedFun = case witNestedFun :: WitNestedFun xs ys r of
                   WitNestedFun -> WitNestedFun
  {-# INLINE witNestedFun #-}
  witLenWrap :: forall f. WitLenWrap f (x ': xs)
  witLenWrap = case witLenWrap :: WitLenWrap f xs of
                 WitLenWrap -> WitLenWrap


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
  default construct :: (Generic v, GHVector (Rep v), GElems (Rep v) ~ Elems v, Functor (Fun (Elems v)))
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

-- | Conversion between homogeneous and heterogeneous type functions.
class (F.Arity n, Arity (HomList n a)) => HomArity n a where
  -- | Convert n-ary homogeneous function to heterogeneous.
  toHeterogeneous :: F.Fun n a r -> Fun (HomList n a) r
  -- | Convert heterogeneous n-ary function to homogeneous.
  toHomogeneous   :: Fun (HomList n a) r -> F.Fun n a r


instance HomArity Z a where
  toHeterogeneous = coerce
  toHomogeneous   = coerce
  {-# INLINE toHeterogeneous #-}
  {-# INLINE toHomogeneous   #-}

instance HomArity n a => HomArity (S n) a where
  toHeterogeneous f
    = Fun $ \a -> unFun $ toHeterogeneous (F.apFun f a)
  toHomogeneous (f :: Fun (a ': HomList n a) r)
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


----------------------------------------------------------------
-- CPS-encoded vectors
----------------------------------------------------------------

-- | CPS-encoded heterogeneous vector.
newtype ContVec xs = ContVec { runContVec :: forall r. Fun xs r -> r }

instance Arity xs => HVector (ContVec xs) where
  type Elems (ContVec xs) = xs
  construct = Fun $
    accum (\(T_mkN f) x -> T_mkN (f . cons x))
          (\(T_mkN f)   -> f (ContVec unFun))
          (T_mkN id :: T_mkN xs xs)
  inspect (ContVec cont) f = cont f
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



toContVec :: ContVecF xs f -> ContVec (Wrap f xs)
toContVec (ContVecF cont) = ContVec $ cont . TFun . unFun
{-# INLINE toContVec #-}

toContVecF :: ContVec (Wrap f xs) -> ContVecF xs f
toContVecF (ContVec cont) = ContVecF $ cont . Fun . unTFun
{-# INLINE toContVecF #-}

-- | Cons element to the vector
cons :: x -> ContVec xs -> ContVec (x ': xs)
cons x (ContVec cont) = ContVec $ \f -> cont $ curryFun f x
{-# INLINE cons #-}

-- | Cons element to the vector
consF :: f x -> ContVecF xs f -> ContVecF (x ': xs) f
consF x (ContVecF cont) = ContVecF $ \f -> cont $ curryTFun f x
{-# INLINE consF #-}



----------------------------------------------------------------
-- Instances of Fun
----------------------------------------------------------------

instance (Arity xs) => Functor (Fun xs) where
  fmap (f :: a -> b) (Fun g0 :: Fun xs a)
    = Fun $ accum (\(T_fmap g) a -> T_fmap (g a))
                  (\(T_fmap r)   -> f r)
                  (T_fmap g0 :: T_fmap a xs)
  {-# INLINE fmap #-}

instance Arity xs => Applicative (Fun xs) where
  pure r = Fun $ accum (\T_pure _ -> T_pure)
                       (\T_pure   -> r)
                       (T_pure :: T_pure xs)
  (Fun f0 :: Fun xs (a -> b)) <*> (Fun g0 :: Fun xs a)
    = Fun $ accum (\(T_ap f g) a -> T_ap (f a) (g a))
                  (\(T_ap f g)   -> f g)
                  ( T_ap f0 g0 :: T_ap (a -> b) a xs)
  {-# INLINE pure  #-}
  {-# INLINE (<*>) #-}

instance Arity xs => Monad (Fun xs) where
  return  = pure
  f >>= g = shuffleF g <*> f
  {-# INLINE return #-}
  {-# INLINE (>>=)  #-}

newtype T_fmap a   xs = T_fmap (Fn xs a)
data    T_pure     xs = T_pure
data    T_ap   a b xs = T_ap (Fn xs a) (Fn xs b)


instance (Arity xs) => Functor (TFun f xs) where
  fmap (f :: a -> b) (TFun g0 :: TFun f xs a)
    = TFun $ accumTy (\(TF_fmap g) a -> TF_fmap (g a))
                     (\(TF_fmap r)   -> f r)
                     (TF_fmap g0 :: TF_fmap f a xs)
  {-# INLINE fmap #-}

instance (Arity xs) => Applicative (TFun f xs) where
  pure r = TFun $ accumTy step
                          (\TF_pure   -> r)
                          (TF_pure :: TF_pure f xs)
    where
      step :: forall a as. TF_pure f (a ': as) -> f a -> TF_pure f as
      step _ _ = TF_pure
  {-# INLINE pure  #-}
  (TFun f0 :: TFun f xs (a -> b)) <*> (TFun g0 :: TFun f xs a)
    = TFun $ accumTy (\(TF_ap f g) a -> TF_ap (f a) (g a))
                  (\(TF_ap f g)   -> f g)
                  ( TF_ap f0 g0 :: TF_ap f (a -> b) a xs)
  {-# INLINE (<*>) #-}

instance Arity xs => Monad (TFun f xs) where
  return  = pure
  f >>= g = shuffleTF g <*> f
  {-# INLINE return #-}
  {-# INLINE (>>=)  #-}

newtype TF_fmap f a   xs = TF_fmap (Fn (Wrap f xs) a)
data    TF_pure f     xs = TF_pure
data    TF_ap   f a b xs = TF_ap (Fn (Wrap f xs) a) (Fn (Wrap f xs) b)



----------------------------------------------------------------
-- Operations on Fun
----------------------------------------------------------------

-- | Apply single parameter to function
curryFun :: Fun (x ': xs) r -> x -> Fun xs r
curryFun (Fun f) x = Fun (f x)
{-# INLINE curryFun #-}

-- | Uncurry N-ary function.
uncurryFun :: (x -> Fun xs r) -> Fun (x ': xs) r
uncurryFun = Fun . fmap unFun
{-# INLINE uncurryFun #-}

uncurryFun2 :: (Arity xs)
            => (x -> y -> Fun xs (Fun ys r))
            -> Fun (x ': xs) (Fun (y ': ys) r)
uncurryFun2 = uncurryFun . fmap (fmap uncurryFun . shuffleF)
{-# INLINE uncurryFun2 #-}

-- | Conversion function
uncurryMany :: forall xs ys r. Arity xs => Fun xs (Fun ys r) -> Fun (xs ++ ys) r
{-# INLINE uncurryMany #-}
uncurryMany f =
  case witNestedFun :: WitNestedFun xs ys r of
    WitNestedFun ->
      case fmap unFun f :: Fun xs (Fn ys r) of
        Fun g -> Fun g

-- | Curry first /n/ arguments of N-ary function.
curryMany :: forall xs ys r. Arity xs => Fun (xs ++ ys) r -> Fun xs (Fun ys r)
{-# INLINE curryMany #-}
curryMany (Fun f0)
  = Fun $ accum (\(T_curry f) a -> T_curry (f a))
                (\(T_curry f)   -> Fun f :: Fun ys r)
                (T_curry f0 :: T_curry r ys xs)

newtype T_curry r ys xs = T_curry (Fn (xs ++ ys) r)


-- | Add one parameter to function which is ignored.
constFun :: Fun xs r -> Fun (x ': xs) r
constFun = uncurryFun . const
{-# INLINE constFun #-}

-- | Transform function but leave outermost parameter untouched.
stepFun :: (Fun xs a -> Fun ys b) -> Fun (x ': xs) a -> Fun (x ': ys) b
stepFun g = uncurryFun . fmap g . curryFun
{-# INLINE stepFun #-}

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
shuffleF fun = Fun $ accum
  (\(T_shuffle f) a -> T_shuffle (\x -> f x a))
  (\(T_shuffle f)   -> f)
  (T_shuffle (fmap unFun fun) :: T_shuffle x r xs)

data T_shuffle x r xs = T_shuffle (Fn (x ': xs) r)

-- | Helper for lens implementation.
lensWorkerF :: forall f r x y xs. (Functor f, Arity xs)
            => (x -> f y) -> Fun (y ': xs) r -> Fun (x ': xs) (f r)
{-# INLINE lensWorkerF #-}
lensWorkerF g f
  = uncurryFun
  $ \x -> (\r -> fmap (r $) (g x)) <$> shuffleF (curryFun f)



----------------------------------------------------------------
-- Operations on TFun
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
uncurryTFun2 = uncurryTFun . fmap (fmap uncurryTFun . shuffleTF)
{-# INLINE uncurryTFun2 #-}


-- | Move first argument of function to its result. This function is
--   useful for implementation of lens.
shuffleTF :: forall f x xs r. Arity xs
          => (x -> TFun f xs r) -> TFun f xs (x -> r)
{-# INLINE shuffleTF #-}
shuffleTF fun0 = TFun $ accumTy
  (\(TF_shuffle f) a -> TF_shuffle (\x -> f x a))
  (\(TF_shuffle f)   -> f)
  (TF_shuffle (fmap unTFun fun0) :: TF_shuffle f x r xs)

data TF_shuffle f x r xs = TF_shuffle (x -> (Fn (Wrap f xs) r))



----------------------------------------------------------------
-- Indexing
----------------------------------------------------------------

-- | Indexing of vectors
class Index (n :: *) (xs :: [*]) where
  type ValueAt n xs :: *
  -- | Getter function for vectors
  getF :: n -> Fun xs (ValueAt n xs)
  -- | Putter function. It applies value @x@ to @n@th parameter of
  --   function.
  putF :: n -> ValueAt n xs -> Fun xs r -> Fun xs r
  -- | Helper for implementation of lens
  lensF :: (Functor f, v ~ ValueAt n xs)
        => n -> (v -> f v) -> Fun xs r -> Fun xs (f r)
  witWrapIndex :: WitWrapIndex f n xs


-- | Proofs for the indexing of wrapped type lists.
data WitWrapIndex f n xs where
  WitWrapIndex :: ( ValueAt n (Wrap f xs) ~ f (ValueAt n xs)
                  , Index n (Wrap f xs)
                  , Arity (Wrap f xs)
                  ) => WitWrapIndex f n xs


instance Arity xs => Index Z (x ': xs) where
  type ValueAt Z (x ': xs) = x
  getF  _     = Fun $ \x -> unFun (pure x :: Fun xs x)
  putF  _ x f = constFun $ curryFun f x
  lensF _     = lensWorkerF
  {-# INLINE getF  #-}
  {-# INLINE putF  #-}
  {-# INLINE lensF #-}
  witWrapIndex :: forall f. WitWrapIndex f Z (x ': xs)
  witWrapIndex = case witWrapped :: WitWrapped f xs of
                   WitWrapped -> WitWrapIndex
  {-# INLINE witWrapIndex #-}

instance Index n xs => Index (S n) (x ': xs) where
  type ValueAt  (S n) (x ': xs) = ValueAt n xs
  getF  _   = constFun $ getF  (undefined :: n)
  putF  _ x = stepFun  $ putF  (undefined :: n) x
  lensF _ f = stepFun  $ lensF (undefined :: n) f
  {-# INLINE getF  #-}
  {-# INLINE putF  #-}
  {-# INLINE lensF #-}
  witWrapIndex :: forall f. WitWrapIndex f (S n) (x ': xs)
  witWrapIndex = case witWrapIndex :: WitWrapIndex f n xs of
                   WitWrapIndex -> WitWrapIndex
  {-# INLINE witWrapIndex #-}



----------------------------------------------------------------
-- Instances
----------------------------------------------------------------

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



----------------------------------------------------------------
-- Generics
----------------------------------------------------------------

class GHVector (v :: * -> *) where
  type GElems v :: [*]
  gconstruct :: Fun (GElems v) (v p)
  ginspect   :: v p -> Fun (GElems v) r -> r


-- We simply skip metadata
instance (GHVector f, Functor (Fun (GElems f))) => GHVector (M1 i c f) where
  type GElems (M1 i c f) = GElems f
  gconstruct = fmap M1 gconstruct
  ginspect v = ginspect (unM1 v)
  {-# INLINE gconstruct #-}
  {-# INLINE ginspect   #-}


instance ( GHVector f, GHVector g
         , Arity xs, GElems f ~ xs
         , Arity ys, GElems g ~ ys
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
  gconstruct = Fun K1
  ginspect (K1 x) (Fun f) = f x
  {-# INLINE gconstruct #-}
  {-# INLINE ginspect   #-}


-- Unit types are empty vectors
instance GHVector U1 where
  type GElems U1 = '[]
  gconstruct         = Fun U1
  ginspect _ (Fun f) = f
  {-# INLINE gconstruct #-}
  {-# INLINE ginspect   #-}
