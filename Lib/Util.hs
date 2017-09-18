{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}

module Lib.Util (
  module Data.Strict.List,
  module Control.Applicative,
  module Control.Monad,
  module Lens.Micro,
  module Lens.Micro.GHC,
  module Lens.Micro.Mtl,
  angleCount, proceedCount,
  R, S1,
  (+~), (*~), fmod, mix,
  (??),
  io,
  zip, zipWith, head, tail, last, (++), concat,
  V1(..), V2(..), V3(..), V4(..),
  Space(..), Arith(..), Linear, Euclidean,
  Field(..)
) where

import Prelude hiding (length, zip, zipWith, head, tail, last, (++), concat)
import Data.Strict.List
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

(??) :: (a -> b -> c) -> b -> a -> c
(f ?? y) x = f x y

io :: MonadIO m => IO a -> m a
io = liftIO

zip :: List a -> List b -> List (a,b)
zip (x:!xs) (y:!ys) = (x,y) :! zip xs ys
zip _ _ = []

zipWith :: (a -> b -> c) -> List a -> List b -> List c
zipWith f (x:!xs) (y:!ys) = f x y :! zipWith f xs ys
zipWith _ _ _ = []

head :: List a -> a
head (x:!xs) = x
head _ = error "head : empty list"

tail :: List a -> List a
tail (x:!xs) = xs
tail _ = error "tail : empty list"

last :: List a -> a
last (x:!Nil) = x
last (x:!xs) = last xs
last _ = error "last : empty list"

(++) :: List a -> List a -> List a
Nil ++ ys = ys
(x:!xs) ++ ys = x :! xs ++ ys

concat :: List (List a) -> List a
concat Nil = Nil
concat (xs:!xss) = xs ++ concat xss

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
