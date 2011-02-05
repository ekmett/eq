{-# LANGUAGE GADTs, TypeOperators #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Eq.Type
-- Copyright   :  (C) 2011 Edward Kmett, Dan Doel
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs, type operators
--
----------------------------------------------------------------------------

module Data.Eq.Type
  ( 
  -- * Equality
    (:=)(..)
  -- * Equality as an equivalence relation
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
  ) where

import Prelude ()
import Control.Category 
import Data.Semigroupoid

infixl 4 :=

data a := b where
  Refl :: a := a

subst :: (a := b) -> p a -> p b
subst Refl pa = pa

trans :: (a := b) -> (b := c) -> (a := c)
trans Refl Refl = Refl

symm :: (a := b) -> b := a
symm Refl = Refl

coerce :: (a := b) -> a -> b
coerce Refl x = x

lift :: a := b -> (f a := f b)
lift Refl = Refl

lift2 :: a := b -> (f a c := f b c)
lift2 Refl = Refl

lift2' :: (a := b) -> (c := d) -> f a c := f b d
lift2' Refl Refl = Refl

lift3 :: (a := b) -> (f a c d := f b c d)
lift3 Refl = Refl

lift3' :: (a := b) -> (c := d) -> (e := f) -> (g a c e := g b d f)
lift3' Refl Refl Refl = Refl

lower :: (f a := f b) -> (a := b)
lower Refl = Refl

lower2 :: (f a c := f b c) -> (a := b)
lower2 Refl = Refl

lower3 :: (f a c d := f b c d) -> (a := b)
lower3 Refl = Refl

instance Category (:=) where
  id = Refl
  (.) = subst

instance Semigroupoid (:=) where
  o = subst
