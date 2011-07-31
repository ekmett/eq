{-# LANGUAGE CPP, Rank2Types, TypeOperators #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Eq.Type
-- Copyright   :  (C) 2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  rank2 types, type operators, (optional) type families
--
-- Leibnizian equality. Injectivity in the presence of type families 
-- is provided by a generalization of a trick by Oleg Kiselyv posted here:
--
-- <http://www.haskell.org/pipermail/haskell-cafe/2010-May/077177.html>
----------------------------------------------------------------------------

module Data.Eq.Type
  ( 
  -- * Leibnizian equality
    (:=)(..)
  -- * Equality as an equivalence relation
  , refl
  , trans
  , symm 
  , coerce
  -- * Lifting equality
  , lift
  , lift2, lift2'
  , lift3, lift3'
#ifdef LANGUAGE_TypeFamilies
  -- * Lowering equality
  , lower
  , lower2
  , lower3
#endif
  ) where

import Prelude ()
import Control.Category 
import Data.Semigroupoid
import Data.Groupoid

infixl 4 :=

-- | Leibnizian equality states that two things are equal if you can 
-- substite one for the other in all contexts
data a := b = Refl { subst :: forall c. c a -> c b } 

-- | Equality is reflexive
refl :: a := a
refl = Refl id

newtype Coerce a = Coerce { uncoerce :: a } 
-- | If two things are equal you can convert one to the other
coerce :: a := b -> a -> b
coerce f = uncoerce . subst f . Coerce

-- | Equality forms a category
instance Category (:=) where
  id = Refl id
  (.) = subst

instance Semigroupoid (:=) where
  o = subst

instance Groupoid (:=) where
  inv = symm

-- | Equality is transitive
trans :: a := b -> b := c -> a := c
trans = (>>>)

newtype Symm p a b = Symm { unsymm :: p b a } 
-- | Equality is symmetric
symm :: (a := b) -> (b := a)
symm a = unsymm (subst a (Symm id))

newtype Lift f a b = Lift { unlift :: f a := f b } 
-- | You can lift equality into any type constructor
lift :: a := b -> f a := f b
lift a = unlift (subst a (Lift id))

newtype Lift2 f c a b = Lift2 { unlift2 :: f a c := f b c }  
-- | ... in any position
lift2 :: a := b -> f a c := f b c
lift2 a = unlift2 (subst a (Lift2 id))

lift2' :: a := b -> c := d -> f a c := f b d
lift2' ab cd = lift2 ab . lift cd

newtype Lift3 f c d a b = Lift3 { unlift3 :: f a c d := f b c d } 
lift3 :: a := b -> f a c d := f b c d
lift3 a = unlift3 (subst a (Lift3 id))

lift3' :: a := b -> c := d -> e := f -> g a c e := g b d f
lift3' ab cd ef = lift3 ab . lift2 cd . lift ef

#ifdef LANGUAGE_TypeFamilies

type family Inj f :: *
type instance Inj (f a) = a
newtype Lower a b = Lower { unlower :: Inj a := Inj b }
-- | Type constructors are injective, so you can lower equality through any type constructor
lower :: f a := f b -> a := b
lower eq = unlower (subst eq (Lower id :: Lower (f a) (f a)))

type family Inj2 f :: *
type instance Inj2 (f a b) = a
newtype Lower2 a b = Lower2 { unlower2 :: Inj2 a := Inj2 b }
-- | ... in any position
lower2 :: f a c := f b c -> a := b
lower2 eq = unlower2 (subst eq (Lower2 id :: Lower2 (f a c) (f a c)))

type family Inj3 f :: *
type instance Inj3 (f a b c) = a
newtype Lower3 a b = Lower3 { unlower3 :: Inj3 a := Inj3 b }
lower3 :: f a c d := f b c d -> a := b
lower3 eq = unlower3 (subst eq (Lower3 id :: Lower3 (f a c d) (f a c d)))

#endif
