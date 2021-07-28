{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Eq.Type.Hetero
-- Copyright   :  (C) 2011-2014 Edward Kmett, 2018 Ryan Scott
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GHC
--
-- Leibnizian equality à la "Data.Eq.Type", generalized to be heterogeneous
-- using higher-rank kinds.
--
-- This module is only exposed on GHC 8.2 and later.
----------------------------------------------------------------------------
module Data.Eq.Type.Hetero
  (
  -- * Heterogeneous Leibnizian equality
    (:==)(..)
  -- * Equality as an equivalence relation
  , refl
  , trans
  , symm
  , coerce
  -- * Lifting equality
  , lift
  , lift2, lift2'
  , lift3, lift3'
  -- * Lowering equality
  , lower
  , lower2
  , lower3
  -- * 'ET.:=' equivalence
  -- | 'ET.:=' is equivalent in power
  , toHomogeneous
  , fromHomogeneous
  -- * 'Eq.:~:' equivalence
  -- | 'Eq.:~:' is equivalent in power
  , fromLeibniz
  , toLeibniz
  -- * 'Eq.:~~:' equivalence
  -- | 'Eq.:~~:' is equivalent in power
  , heteroFromLeibniz
  , heteroToLeibniz
  -- * 'Co.Coercion' conversion
  -- | Leibnizian equality can be converted to representational equality
  , reprLeibniz
  ) where

import           Control.Category
import           Data.Groupoid
import           Data.Semigroupoid
import qualified Data.Type.Coercion as Co
import qualified Data.Type.Equality as Eq
import           Data.Kind
import qualified Data.Eq.Type as ET
import           GHC.Exts (Any)
import           Prelude hiding (id, (.))

infixl 4 :==

-- | Heterogeneous Leibnizian equality.
--
-- Leibnizian equality states that two things are equal if you can
-- substitute one for the other in all contexts.
newtype (a :: j) :== (b :: k)
  = HRefl { hsubst :: forall (c :: forall i. i -> Type). c a -> c b }
type role (:==) nominal nominal

-- | Equality is reflexive.
refl :: a :== a
refl = HRefl id

newtype Coerce (a :: k) = Coerce { uncoerce :: MassageKind Type a }

type family MassageKind (j :: Type) (a :: k) :: j where
  MassageKind j (a :: j) = a
  MassageKind _ _        = Any

-- | If two things are equal, you can convert one to the other.
coerce :: a :== b -> a -> b
coerce f = uncoerce . hsubst f . Coerce

newtype Push :: (forall j k. j -> k -> Type)
             -> forall j. j -> forall k. k -> Type where
  Push :: forall (p :: forall j k. j -> k -> Type)
                 j k (a :: j) (b :: k).
          { unpush :: p a b } -> Push p a b

-- | Equality is compositional.
comp :: b :== c -> a :== b -> a :== c
comp f = unpush . hsubst f . Push

-- | Equality forms a category.
instance Category (:==) where
  id  = refl
  (.) = comp

instance Semigroupoid (:==) where
  o = comp

instance Groupoid (:==) where
  inv = symm

-- | Equality is transitive.
trans :: a :== b -> b :== c -> a :== c
trans = flip comp

newtype Symm :: (forall j. j -> forall k. k -> Type)
             ->  forall j. j -> forall k. k -> Type where
  Symm :: forall (p :: forall j. j -> forall k. k -> Type)
                 j k (a :: j) (b :: k).
          { unsymm :: p b a } -> Symm p a b

-- | Equality is symmetric.
symm :: a :== b -> b :== a
symm ab = unpush $ unsymm $ hsubst ab $ Symm $ Push refl

newtype Lift :: forall j r.
                (j -> r) -> j
             -> forall k. k
             -> Type where
  Lift :: forall j r k (f :: j -> r) (a :: j) (b :: k).
          { unlift :: f a :== f (MassageKind j b) } -> Lift f a b

-- | You can lift equality into any type constructor...
lift :: a :== b -> f a :== f b
lift f = unlift $ hsubst f $ Lift refl

newtype Lift2 :: forall j1 j2 r.
                 (j1 -> j2 -> r) -> j1 -> j2
              -> forall k. k
              -> Type where
  Lift2 :: forall j1 j2 r k
                  (f :: j1 -> j2 -> r) (a :: j1) (b :: k) (c :: j2).
           { unlift2 :: f a c :== f (MassageKind j1 b) c } -> Lift2 f a c b

-- | ... in any position.
lift2 :: a :== b -> f a c :== f b c
lift2 f = unlift2 $ hsubst f $ Lift2 refl

lift2' :: a :== b -> c :== d -> f a c :== f b d
lift2' ab cd = unpush $ lift2 ab `hsubst` Push (lift cd)

newtype Lift3 :: forall j1 j2 j3 r.
                 (j1 -> j2 -> j3 -> r) -> j1 -> j2 -> j3
              -> forall k. k
              -> Type where
  Lift3 :: forall j1 j2 j3 r k
                  (f :: j1 -> j2 -> j3 -> r) (a :: j1) (b :: k) (c :: j2) (d :: j3).
           { unlift3 :: f a c d :== f (MassageKind j1 b) c d } -> Lift3 f a c d b

lift3 :: a :== b -> f a c d :== f b c d
lift3 f = unlift3 $ hsubst f $ Lift3 refl

lift3' :: a :== b -> c :== d -> e :== f -> g a c e :== g b d f
lift3' ab cd ef = unpush $ unpush (lift3 ab `hsubst` Push (lift2 cd)) `hsubst` Push (lift ef)

newtype Lower :: forall j1 j2 k1 k2.
                 (j1 -> j2) -> (k1 -> k2)
              -> forall j2'. j2' -> forall k2'. k2'
              -> Type where
  Lower :: { unlower :: a :== GenInj f g x } -> Lower f g a x

type family PickKind (f :: j1 -> j2) (g :: k1 -> k2) (x :: l) :: Type where
  PickKind f _ (f (_ :: j1)) = j1
  PickKind _ g (g (_ :: k1)) = k1
  PickKind _ _ _             = Any

type family GenInj (f :: j1 -> j2) (g :: k1 -> k2) (x :: l) :: PickKind f g x where
  GenInj f _ (f a) = a
  GenInj _ g (g b) = b
  GenInj _ _ _     = Any

-- | Type constructors are generative and injective, so you can lower equality
-- through any type constructors.
lower :: forall a b f g. f a :== g b -> a :== b
lower f = unlower $ hsubst f (Lower refl :: Lower f g a (f a))

newtype Lower2 :: forall j1 j2 j3 k1 k2 k3.
                  (j1 -> j2 -> j3) -> (k1 -> k2 -> k3)
               -> forall j3'. j3' -> forall k3'. k3'
               -> Type where
  Lower2 :: { unlower2 :: a :== GenInj2 f g x } -> Lower2 f g a x

type family PickKind2 (f :: j1 -> j2 -> j3) (g :: k1 -> k2 -> k3) (x :: l) :: Type where
  PickKind2 f _ (f (_ :: j1) _) = j1
  PickKind2 _ g (g (_ :: k1) _) = k1
  PickKind2 _ _ _               = Any

type family GenInj2 (f :: j1 -> j2 -> j3) (g :: k1 -> k2 -> k3) (x :: l) :: PickKind2 f g x where
  GenInj2 f _ (f a _) = a
  GenInj2 _ g (g b _) = b
  GenInj2 _ _ _       = Any

lower2 :: forall a b f g c c'. f a c :== g b c' -> a :== b
lower2 f = unlower2 $ hsubst f (Lower2 refl :: Lower2 f g a (f a c))

newtype Lower3 :: forall j1 j2 j3 j4 k1 k2 k3 k4.
                  (j1 -> j2 -> j3 -> j4) -> (k1 -> k2 -> k3 -> k4)
               -> forall j4'. j4' -> forall k4'. k4'
               -> Type where
  Lower3 :: { unlower3 :: a :== GenInj3 f g x } -> Lower3 f g a x

type family PickKind3 (f :: j1 -> j2 -> j3 -> j4) (g :: k1 -> k2 -> k3 -> k4) (x :: l) :: Type where
  PickKind3 f _ (f (_ :: j1) _ _) = j1
  PickKind3 _ g (g (_ :: k1) _ _) = k1
  PickKind3 _ _ _                 = Any

type family GenInj3 (f :: j1 -> j2 -> j3 -> j4) (g :: k1 -> k2 -> k3 -> k4) (x :: l) :: PickKind3 f g x where
  GenInj3 f _ (f a _ _) = a
  GenInj3 _ g (g b _ _) = b
  GenInj3 _ _ _         = Any

lower3 :: forall a b f g c c' d d'. f a c d :== g b c' d' -> a :== b
lower3 f = unlower3 $ hsubst f (Lower3 refl :: Lower3 f g a (f a c d))

newtype Flay :: forall j.
                (j -> j -> Type) -> j
             -> forall k. k
             -> Type where
  Flay :: forall j k (p :: j -> j -> Type) (a :: j) (b :: k).
          { unflay :: p a (MassageKind j b) } -> Flay p a b

-- | Convert an appropriately kinded heterogeneous Leibnizian equality into
-- a homogeneous Leibnizian equality '(ET.:=)'.
toHomogeneous :: a :== b -> a ET.:= b
toHomogeneous f = unflay $ hsubst f $ Flay ET.refl

-- | Convert a homogeneous Leibnizian equality '(ET.:=)' to an appropriately kinded
-- heterogeneous Leibizian equality.
fromHomogeneous :: a ET.:= b -> a :== b
fromHomogeneous f = ET.subst f refl

fromLeibniz :: forall a b. a :== b -> a Eq.:~: b
fromLeibniz f = unflay $ hsubst f $ Flay Eq.Refl

toLeibniz :: a Eq.:~: b -> a :== b
toLeibniz Eq.Refl = refl

heteroFromLeibniz :: a :== b -> a Eq.:~~: b
heteroFromLeibniz f = unpush $ hsubst f $ Push $ Eq.HRefl

heteroToLeibniz :: a Eq.:~~: b -> a :== b
heteroToLeibniz Eq.HRefl = refl

instance Eq.TestEquality ((:==) a) where
  testEquality fa fb = Just (fromLeibniz (trans (symm fa) fb))

reprLeibniz :: a :== b -> Co.Coercion a b
reprLeibniz f = unflay $ hsubst f $ Flay Co.Coercion

instance Co.TestCoercion ((:==) a) where
  testCoercion fa fb = Just (reprLeibniz (trans (symm fa) fb))
