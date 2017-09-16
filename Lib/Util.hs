{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Lib.Util (
  module Control.Applicative,
  module Control.Monad,
  module Lens.Micro,
  module Lens.Micro.GHC,
  module Lens.Micro.Mtl,
  angleCount, proceedCount,
  R, S1,
  (+~), (*~), fmod, (??), mix,
  io,
  V1(..), V2(..), V3(..), V4(..),
  Space(..), Arith(..), Linear, Euclidean,
  Field(..)
) where

import Prelude hiding (length)
import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Lens.Micro
import Lens.Micro.GHC
import Lens.Micro.Mtl
import Haste.Foreign

angleCount :: Int
angleCount = constant "angleCount"
proceedCount :: Int
proceedCount = constant "proceedCount"

type R = Double
type S1 = R

(+~) :: Num a => ASetter s s a a -> a -> s -> s
l +~ x = l %~ (+x)
infix 4 +~

(*~) :: Num a => ASetter s s a a -> a -> s -> s
l *~ x = l %~ (*x)
infix 4 *~

fmod :: RealFrac a => a -> a -> a
fmod e m = e + (-1) * fromIntegral (floor (e/m)) * m

mix :: Num a => a -> a -> a -> a
mix a b x = a + (b - a) * x

io :: MonadIO m => IO a -> m a
io = liftIO

(??) :: (a -> b -> c) -> b -> a -> c
(f ?? y) x = f x y

class V1 a b | a -> b where
  x :: Lens' a b
class V1 a b => V2 a b | a -> b where
  y :: Lens' a b
class V2 a b => V3 a b | a -> b where
  z :: Lens' a b
class V3 a b => V4 a b | a -> b where
  w :: Lens' a b

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

type Field a = (Floating a, Ord a)
type Linear f a = (Applicative f, Space f, Field a)
type Euclidean f a = (Linear f a, Arith f)
