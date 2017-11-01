{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
-- | Type functions
module Data.Vector.HFixed.TypeFuns (
    -- * Type proxy
    Proxy(..)
  , proxy
    -- * Type functions
  , type (++)
  , Len
  , Head
  , HomList
  ) where

import Data.Typeable          (Proxy(..))
import Data.Vector.Fixed.Cont (S,Z)

proxy :: t -> Proxy t
proxy _ = Proxy


-- | Concaternation of type level lists.
type family   (++) (xs :: [α]) (ys :: [α]) :: [α] where
  (++) '[]      ys = ys
  (++) (x : xs) ys = x : xs ++ ys


-- | Length of type list expressed as type level naturals from
--   @fixed-vector@.
type family   Len (xs :: [α]) where
  Len '[]      = Z
  Len (x : xs) = S (Len xs)

-- | Head of type list
type family   Head (xs :: [α]) :: α where
  Head (x : xs) = x


-- | Homogeneous type list with length /n/ and element of type /a/. It
--   uses type level natural defined in @fixed-vector@.
type family   HomList n (a :: α) :: [α] where
  HomList  Z    a = '[]
  HomList (S n) a = a : HomList n a



