{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor #-}

module Lib.World where

import Prelude hiding (length)
import Lib.Util
import Lib.AD
import Data.Monoid

data World a = World a a a
  deriving (Show, Functor)

instance Applicative World where
  pure s = World s s s
  World f g h <*> World x y z = World (f x) (g y) (h z)

instance Foldable World where
  foldMap f (World x y z) = f x <> f y <> f z

instance Num a => Num (World a) where
  (+) = liftA2 (+)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  fromInteger p = pure 0

instance Space World where
  basis = World (World 1 0 0) (World 0 1 0) (World 0 0 1)

instance Arith World where
  scale = pure
  dot (World x1 y1 z1) (World x2 y2 z2) = x1*x2+y1*y2+z1*z2

instance V1 (World a) a where
  x = lens (\(World x _ _) -> x) $ \(World _ y z) v -> World v y z
instance V2 (World a) a where
  y = lens (\(World _ y _) -> y) $ \(World x _ z) v -> World x v z
instance V3 (World a) a where
  z = lens (\(World _ _ z) -> z) $ \(World x y _) v -> World x y v

field :: Field a => World a -> a
-- field p = length p - 1 -- Sphere
field (World x y z) = let
    qx = sqrt (x^2+z^2) - 0.8
    qy = y
  in sqrt (qx^2 + qy^2) - 0.5

gradient :: Field a => World a -> World a
gradient = grad field

distance :: Field a => World a -> a
distance p = field p / norm (gradient p)

normal :: Field a => World a -> World a
normal p = normalize $ gradient p
