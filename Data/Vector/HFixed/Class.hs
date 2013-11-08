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
    Fn
  , Fun(..)
    -- ** Type proxy
  , Proxy(..)
  , proxy
  , unproxy
    -- ** Type functions
  , (++)()
  , Len
  , Head
  , HomList
  , Wrap
    -- ** Type classes
  , Arity(..)
  , HVector(..)
    -- ** Interop with homogeneous vectors
  , HomArity(..)
  , homInspect
  , homConstruct
    -- * Operations of Fun
    -- ** Recursion primitives
  , curryFun
  , uncurryFun
  , uncurryFun2
  , curryMany
  , constFun
  , stepFun
    -- ** More complicated functions
  , concatF
  , shuffleF
  , lensF
  , Index(..)
    -- * Folds and unfolds
  , Foldr(..)
  , Unfoldr(..)
    -- * Map and zip
  , Apply(..)
  , Apply2(..)
  , Apply2Mono(..)
  , Map(..)
  , MapRes
  , Zip(..)
  , ZipRes
  , ZipMono(..)
    -- * Isomorphism between types
  , NatIso(..)
  ) where

import Control.Applicative (Applicative(..))
import Data.Complex        (Complex(..))

import           Data.Vector.Fixed   (S,Z)
import qualified Data.Vector.Fixed                as F
import qualified Data.Vector.Fixed.Cont           as F (apFun)
import qualified Data.Vector.Fixed.Unboxed        as U
import qualified Data.Vector.Fixed.Primitive      as P
import qualified Data.Vector.Fixed.Storable       as S
import qualified Data.Vector.Fixed.Boxed          as B

import GHC.Generics hiding (Arity(..),S)
import GHC.TypeLits
import GHC.Prim            (Constraint)



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



----------------------------------------------------------------
-- Type families
----------------------------------------------------------------

-- | Kind polymorphic proxy.
data Proxy (a :: α) = Proxy

proxy :: t -> Proxy t
proxy _ = Proxy

unproxy :: Proxy t -> t
unproxy _ = error "Data.Vector.HFixed.Class: unproxied value"


-- | Concaternation of type level lists.
type family   (++) (xs :: [*]) (ys :: [*]) :: [*]
type instance (++) '[]       ys = ys
type instance (++) (x ': xs) ys = x ': xs ++ ys


-- | Length of type list expressed as type level naturals from
--   @fixed-vector@.
type family   Len (xs :: [α]) :: *
type instance Len '[]       = Z
type instance Len (x ': xs) = S (Len xs)

-- | Head of type list
type family   Head (xs :: [α]) :: α
type instance Head (x ': xs) = x


-- | Homogeneous type list with length @n@ and element type @a@.
type family   HomList n (a :: α) :: [α]
type instance HomList  Z    a = '[]
type instance HomList (S n) a = a ': HomList n a

-- | Wrap every element of list into type constructor
type family   Wrap (f :: α -> β) (a :: [α]) :: [β]
type instance Wrap f  '[]      = '[]
type instance Wrap f (x ': xs) = (f x) ': (Wrap f xs)



----------------------------------------------------------------
-- Generic operations
----------------------------------------------------------------

-- | Type class for dealing with N-ary function in generic way. Since
--   we can't say anything about types of elements most functions
--   implemented in terms of 'accum' and 'apply' can't do anything
--   beyond shuffling function parameters.
--
--   This is also somewhat a kitchen sink module. It contains other
--   inductively defined functions which couldn't be defined in terms
--   of 'accum' and 'apply' but still useful.
class Arity (xs :: [*]) where
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
        -> Fn xs b
           -- ^ N-ary function.
        -> b

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
  arity :: Proxy xs -> Int

  castWrapped :: (Arity (Wrap f xs) => t f xs) -> t f xs

  -- | Conversion function. It could be expressed via accum:
  --
  -- > uncurryF :: forall xs ys r. Fun xs (Fun ys r) -> Fun (xs ++ ys) r
  -- > uncurryF f =
  -- >   case fmap unFun f :: Fun xs (Fn ys r) of
  -- >     Fun g -> Fun g
  --
  -- Alas it requires proving constraint:
  --
  -- > Fn (xs++ys) r ~ Fn xs (Fn ys r)
  --
  -- It is always true but there is no way to tell GHC about it.
  uncurryMany :: Fun xs (Fun ys r) -> Fun (xs ++ ys) r


instance Arity '[] where
  accum   _ f t = f t
  apply   _ _ b = b
  accumTy _ f t = f t
  applyTy _ _ b = b
  {-# INLINE accum   #-}
  {-# INLINE apply   #-}
  {-# INLINE accumTy #-}
  {-# INLINE applyTy #-}
  arity _     = 0
  {-# INLINE arity #-}
  castWrapped x = x
  {-# INLINE castWrapped #-}
  uncurryMany = unFun
  {-# INLINE uncurryMany #-}

instance Arity xs => Arity (x ': xs) where
  accum   f g t = \a -> accum f g (f t a)
  apply   f t h = case f t of (a,u) -> apply f u (h a)
  accumTy f g t = \a -> accumTy f g (f t a)
  applyTy f t h = case f t of (a,u) -> applyTy f u (h a)
  {-# INLINE accum   #-}
  {-# INLINE apply   #-}
  {-# INLINE accumTy #-}
  {-# INLINE applyTy #-}
  arity _     = 1 + arity (Proxy :: Proxy xs)
  {-# INLINE arity        #-}
  castWrapped x = unStep $ castWrapped $ Step x
  {-# INLINE castWrapped #-}
  uncurryMany f = Fun $ unFun . uncurryMany . curryFun f
  {-# INLINE uncurryMany #-}

newtype Step t x f xs = Step { unStep :: t f (x ': xs) }



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
-- On the surface it makes sence to add constraint @Arity (Elems v)@
-- but it bring problems. For example when working with vectors
-- paramterized by functor constraints like @Arity (Wrap f (Elems v))@
-- arise. And they make writing code fully polymorphic in @f@ impossible.
--
-- Default implementation which uses 'Generic' is provided.
class HVector v where
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



----------------------------------------------------------------
-- Interop with homogeneous vectors
----------------------------------------------------------------

-- | Conversion between homgeneous and heterogeneous type functions.
class (F.Arity n, Arity (HomList n a)) => HomArity n a where
  -- | Convert n-ary homogeneous function to heterogeneous.
  toHeterogeneous :: F.Fun n a r -> Fun (HomList n a) r
  -- | Convert heterogeneous n-ary function to homogeneous.
  toHomogeneous   :: Fun (HomList n a) r -> F.Fun n a r


instance HomArity Z a where
  toHeterogeneous = Fun . F.unFun
  toHomogeneous   = F.Fun . unFun
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
  f >>= g = shuffleF (Fun $ fmap unFun g) <*> f
  {-# INLINE return #-}
  {-# INLINE (>>=)  #-}

newtype T_fmap a   xs = T_fmap (Fn xs a)
data    T_pure     xs = T_pure
data    T_ap   a b xs = T_ap (Fn xs a) (Fn xs b)




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
uncurryFun2 = uncurryFun . fmap (fmap uncurryFun . shuffleF . uncurryFun)
{-# INLINE uncurryFun2 #-}

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
shuffleF :: forall x xs r. Arity xs => Fun (x ': xs) r -> Fun xs (x -> r)
{-# INLINE shuffleF #-}
shuffleF (Fun f0) = Fun $ accum
  (\(T_shuffle f) a -> T_shuffle (\x -> f x a))
  (\(T_shuffle f)   -> f)
  (T_shuffle f0 :: T_shuffle x r xs)

data T_shuffle x r xs = T_shuffle (Fn (x ': xs) r)


-- | Helper for lens implementation.
lensF :: forall f r x y xs. (Functor f, Arity xs)
       => (x -> f y) -> Fun (y ': xs) r -> Fun (x ': xs) (f r)
{-# INLINE lensF #-}
lensF fun f = Fun $ \x -> unFun $ fmap (\r -> fmap (r $) (fun x))
                                $ shuffleF f



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

instance Arity xs => Index Z (x ': xs) where
  type ValueAt Z (x ': xs) = x
  getF _     = Fun $ \x -> unFun (pure x :: Fun xs x)
  putF _ x f = constFun $ curryFun f x

instance Index n xs => Index (S n) (x ': xs) where
  type ValueAt  (S n) (x ': xs) = ValueAt n xs
  getF _   = constFun $ getF (undefined :: n)
  putF _ x = stepFun (putF (undefined :: n) x)



----------------------------------------------------------------
-- Folding and unfolding
----------------------------------------------------------------

-- | Generic right fold
class Foldr (c :: * -> Constraint) (xs :: [*]) where
  hfoldrF :: Proxy c -> (forall a. c a => a -> b -> b) -> Fun xs (b -> b)

instance Foldr c '[] where
  hfoldrF _ _ = Fun id
instance (Foldr c xs, c x, Arity xs)  => Foldr c (x ': xs) where
  hfoldrF wit f
    = Fun $ \x -> unFun $ fmap ((f x) . ) (hfoldrF wit f `asFunXS` (Proxy :: Proxy xs))

-- | Type class for unfolding heterogeneous vectors
class Unfoldr (c :: * -> Constraint) (xs :: [*]) where
  unforldrF :: Proxy c
            -> (forall a. c a => b -> (a,b))
            -> Fun xs r
            -> b
            -> r
  unforldrFM :: Monad m
             => Proxy c
             -> (forall a. c a => b -> m (a,b))
             -> Fun xs r
             -> b
             -> m r

instance Unfoldr c '[] where
  unforldrF  _ _ (Fun r) _ = r
  unforldrFM _ _ (Fun r) _ = return r

instance (Unfoldr c xs, c x) => Unfoldr c (x ': xs) where
  -- Simple unfold
  unforldrF wit step (Fun f) b
    = unforldrF wit step (Fun (f x) `asFunXS` (Proxy :: Proxy xs)) b'
    where
      (x,b') = step b
  -- Monadic unfold
  unforldrFM wit step (Fun f) b = do
    (x,b') <- step b
    unforldrFM wit step (Fun (f x) `asFunXS` (Proxy :: Proxy xs)) b'


asFunXS :: Fun xs r -> Proxy xs -> Fun xs r
asFunXS f _ = f

----------------------------------------------------------------
-- Map and zip
----------------------------------------------------------------

class Apply t a where
  type Applied t a :: *
  applyFun :: t -> a -> Applied t a

type family   MapRes t (xs :: [*]) :: [*]
type instance MapRes t '[] = '[]
type instance MapRes t (x ': xs) = Applied t x ': MapRes t xs

class Apply2 t a b where
  type Applied2 t a b :: *
  applyFun2 :: t -> a -> b -> Applied2 t a b

type family   ZipRes t (xs :: [*]) (ys :: [*]) :: [*]
type instance ZipRes t '[] '[] = '[]
type instance ZipRes t (x ': xs) (y ': ys) = Applied2 t x y ': ZipRes t xs ys

class Apply2Mono t a where
  applyFun2Mono :: t -> a -> a -> a



-- | Map for the heterogeneous vectors
class Arity xs => Map t xs where
  mapF :: t -> Fun (MapRes t xs) r -> Fun xs r

instance Map t '[] where
  mapF _ = id
  {-# INLINE mapF #-}
instance (Apply t x, Map t xs) => Map t (x ': xs) where
  mapF t (f :: Fun (MapRes t (x ': xs)) r)
    = Fun $ \x -> unFun (mapF t $ curryFun f $ applyFun t x :: Fun xs r)
  {-# INLINE mapF #-}



-- | Zip for heterogeneous vectors
class (Arity xs, Arity ys) => Zip t xs ys where
  zipF :: t -> Fun (ZipRes t xs ys) r -> Fun xs (Fun ys r)

instance Zip t '[] '[] where
  zipF _ = Fun
  {-# INLINE zipF #-}

instance (Zip t xs ys, Apply2 t x y) => Zip t (x ': xs) (y ': ys) where
  zipF t (f :: Fun (ZipRes t (x ': xs) (y ': ys)) r)
   = uncurryFun2 $ \x y -> (zipF t (curryFun f (applyFun2 t x y)) :: Fun xs (Fun ys r))
  {-# INLINE zipF #-}



-- | Zip for identical vectors
class (Arity xs) => ZipMono t xs where
  zipMonoF :: t -> Fun xs r -> Fun xs (Fun xs r)

instance ZipMono t '[] where
  zipMonoF _ = Fun
  {-# INLINE zipMonoF #-}
instance (ZipMono t xs, Apply2Mono t x) => ZipMono t (x ': xs) where
  zipMonoF t (f :: Fun (x ': xs) r)
    = uncurryFun2 $ \x y -> (zipMonoF t (curryFun f (applyFun2Mono t x y)) :: Fun xs (Fun xs r))
  {-# INLINE zipMonoF #-}



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
-- Isomorphism
----------------------------------------------------------------

-- | Isomorphism between two representations of natural numbers
class (ToNat a ~ b, ToPeano b ~ a) => NatIso (a :: *) (b :: Nat) where
  type ToNat    a :: Nat
  type ToPeano b :: *

instance NatIso (Z) 0 where
  type ToNat (Z) = 0
  type ToPeano 0 = Z

instance NatIso (S (Z)) 1 where
  type ToNat (S (Z)) = 1
  type ToPeano 1 = S (Z)

instance NatIso (S (S (Z))) 2 where
  type ToNat (S (S (Z))) = 2
  type ToPeano 2 = S (S (Z))

instance NatIso (S (S (S (Z)))) 3 where
  type ToNat (S (S (S (Z)))) = 3
  type ToPeano 3 = S (S (S (Z)))

instance NatIso (S (S (S (S (Z))))) 4 where
  type ToNat (S (S (S (S (Z))))) = 4
  type ToPeano 4 = S (S (S (S (Z))))

instance NatIso (S (S (S (S (S (Z)))))) 5 where
  type ToNat (S (S (S (S (S (Z)))))) = 5
  type ToPeano 5 = S (S (S (S (S (Z)))))

instance NatIso (S (S (S (S (S (S (Z))))))) 6 where
  type ToNat (S (S (S (S (S (S (Z))))))) = 6
  type ToPeano 6 = S (S (S (S (S (S (Z))))))

instance NatIso (S (S (S (S (S (S (S (Z)))))))) 7 where
  type ToNat (S (S (S (S (S (S (S (Z)))))))) = 7
  type ToPeano 7 = S (S (S (S (S (S (S (Z)))))))

instance NatIso (S (S (S (S (S (S (S (S (Z))))))))) 8 where
  type ToNat (S (S (S (S (S (S (S (S (Z))))))))) = 8
  type ToPeano 8 = S (S (S (S (S (S (S (S (Z))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (Z)))))))))) 9 where
  type ToNat (S (S (S (S (S (S (S (S (S (Z)))))))))) = 9
  type ToPeano 9 = S (S (S (S (S (S (S (S (S (Z)))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (Z))))))))))) 10 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (Z))))))))))) = 10
  type ToPeano 10 = S (S (S (S (S (S (S (S (S (S (Z))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))) 11 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))) = 11
  type ToPeano 11 = S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))) 12 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))) = 12
  type ToPeano 12 = S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))) 13 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))) = 13
  type ToPeano 13 = S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))) 14 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))) = 14
  type ToPeano 14 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))) 15 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))) = 15
  type ToPeano 15 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))) 16 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))) = 16
  type ToPeano 16 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))) 17 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))) = 17
  type ToPeano 17 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))) 18 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))) = 18
  type ToPeano 18 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))) 19 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))) = 19
  type ToPeano 19 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))



----------------------------------------------------------------
-- Generics
----------------------------------------------------------------

class GHVector v where
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
