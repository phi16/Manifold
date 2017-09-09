{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Lib.Util (
  module Control.Applicative,
  module Control.Monad,
  module Lens.Micro,
  module Lens.Micro.GHC,
  module Lens.Micro.Mtl,
  R,
  (+~), (*~), fmod,
  io,
  V3(..), Space(..), Arith(..), Linear, Euclidean,
  Field(..)
) where

import Prelude hiding (length)
import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Lens.Micro
import Lens.Micro.GHC
import Lens.Micro.Mtl

type R = Double

(+~) :: Num a => ASetter s s a a -> a -> s -> s
l +~ x = l %~ (+x)
infix 4 +~

(*~) :: Num a => ASetter s s a a -> a -> s -> s
l *~ x = l %~ (*x)
infix 4 *~

fmod :: RealFrac a => a -> a -> a
fmod e m = e + (-1) * fromIntegral (floor (e/m)) * m

io :: MonadIO m => IO a -> m a
io = liftIO

class V3 a b | a -> b where
  x :: Lens' a b
  y :: Lens' a b
  z :: Lens' a b

class Space f where
  basis :: Num a => f (f a)

class (Functor f, Space f) => Arith f where
  scale :: Field a => a -> f a
  dot :: Field a => f a -> f a -> a
  norm :: Field a => f a -> a
  norm x = dot x x
  length :: Field a => f a -> a
  length = sqrt . norm
  normalize :: Field a => f a -> f a
  normalize x = let l = length x in fmap (/l) x

type Field a = Floating a
type Linear f a = (Traversable f, Applicative f, Space f, Field a)
type Euclidean f a = (Linear f a, Arith f)
