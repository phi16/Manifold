{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}

module Lib.World where

import Prelude hiding (length)
import Lib.Util
import Lib.AD
import Data.Monoid

data World a = World !a !a !a
  deriving (Show, Functor, Foldable)

instance Applicative World where
  pure s = World s s s
  World f g h <*> World x y z = World (f x) (g y) (h z)

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

cross :: Num a => World a -> World a -> World a
cross (World x1 y1 z1) (World x2 y2 z2) = World (y1*z2-y2*z1) (z1*x2-z2*x1) (x1*y2-x2*y1)

instance V1 (World a) a where
  x = lens (\(World x _ _) -> x) $ \(World _ y z) x -> World x y z
instance V2 (World a) a where
  y = lens (\(World _ y _) -> y) $ \(World x _ z) y -> World x y z
instance V3 (World a) a where
  z = lens (\(World _ _ z) -> z) $ \(World x y _) z -> World x y z

field :: Field a => World a -> a
-- field p = p^.y -- Plane
field p = length p - 1 -- Sphere
{- field (World x y z) = let -- Torus
    qx = sqrt (x^2+z^2) - 0.8
    qy = y
  in sqrt (qx^2 + qy^2) - 0.5 -}
{- field p = let -- Cube
    d = abs p - pure 0.6
  in min 0 ((d^.x)`max`(d^.y)`max`(d^.z)) + length (World (max (d^.x) 0) (max (d^.y) 0) (max (d^.z) 0)) - 0.3 -}
{- field (World x y z) = let -- Pseudo-sphere
    d = sqrt (x^2+z^2)
  in d - exp y -}

gradient :: Field a => World a -> World a
gradient = grad field

distance :: Field a => World a -> a
distance p = field p / norm (gradient p)

normal :: Field a => World a -> World a
normal p = normalize $ gradient p

boundary :: Field a => World a -> a
boundary p = -1 -- sqrt ((p^.x)^2 + (p^.z)^2) - 1

boundGradient :: Field a => World a -> World a
boundGradient = grad boundary

perpTo :: Field a => World a -> World a -> World a
perpTo v n = v - n * scale (dot n v)

fitP :: Field a => World a -> (World a, World a)
fitP p = let
    f = field p
    g = gradient p
    n = normalize g
    d = f / length g
  in (p - n * scale d, n)

fitV :: (Eq a, Field a) => World a -> World a -> World a
fitV n v = let
    l = length v
    d = v`perpTo`n
    longAs v l = if length v == 0 then 0 else normalize v * scale l
  in d`longAs`l

fitR :: Field a => World a -> World a -> World a
fitR n r = normalize $ r`perpTo`n
