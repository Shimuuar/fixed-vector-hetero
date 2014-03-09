{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
-- | Type functions
module Data.Vector.HFixed.TypeFuns (
    -- * Type proxy
    Proxy(..)
  , proxy
  , unproxy
    -- * Type functions
  , (++)()
  , Len
  , Head
  , HomList
  , Wrap
  ) where

import Data.Typeable          (Proxy(..))
import Data.Vector.Fixed.Cont (S,Z)


proxy :: t -> Proxy t
proxy _ = Proxy

unproxy :: Proxy t -> t
unproxy _ = error "Data.Vector.HFixed.Class: unproxied value"


-- | Concaternation of type level lists.
type family   (++) (xs :: [α]) (ys :: [α]) :: [α]
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


-- | Homogeneous type list with length /n/ and element of type /a/. It
--   uses type level natural defined in @fixed-vector@.
type family   HomList n (a :: α) :: [α]
type instance HomList  Z    a = '[]
type instance HomList (S n) a = a ': HomList n a

-- | Wrap every element of list into type constructor
type family   Wrap (f :: α -> β) (a :: [α]) :: [β]
type instance Wrap f  '[]      = '[]
type instance Wrap f (x ': xs) = (f x) ': (Wrap f xs)



