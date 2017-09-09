{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}

module Lib.World where

import Lib.Util
import Lib.AD
import Data.Monoid

data World a = World a a a
  deriving Show

instance Num a => Num (World a) where
  World x1 y1 z1 + World x2 y2 z2 = World (x1+x2) (y1+y2) (z1+z2)
  World x1 y1 z1 * World x2 y2 z2 = World (x1*x2) (y1*y2) (z1*z2)
  negate (World x y z) = World (-x) (-y) (-z)
  abs (World x y z) = World (abs x) (abs y) (abs z)
  signum (World x y z) = World (signum x) (signum y) (signum z)
  fromInteger p = World 0 0 0

instance Space World where
  basis = World (World 1 0 0) (World 0 1 0) (World 0 0 1)

instance Arith World where
  scale s = World s s s
  dot (World x1 y1 z1) (World x2 y2 z2) = x1*x2+y1*y2+z1*z2

instance V3 (World a) a where
  x = lens (\(World x _ _) -> x) $ \(World _ y z) v -> World v y z
  y = lens (\(World _ y _) -> y) $ \(World x _ z) v -> World x v z
  z = lens (\(World _ _ z) -> z) $ \(World x y _) v -> World x y v

instance Functor World where
  fmap f (World x y z) = World (f x) (f y) (f z)

instance Applicative World where
  pure s = World s s s
  World f g h <*> World x y z = World (f x) (g y) (h z)

instance Foldable World where
  foldMap f (World x y z) = f x <> f y <> f z

instance Traversable World where
  traverse f (World x y z) = World <$> f x <*> f y <*> f z

field :: Field a => World a -> a
field p = norm p - 1

gradient :: Field a => World a -> World a
gradient = grad field

distance :: Field a => World a -> a
distance p = field p / norm (gradient p)
