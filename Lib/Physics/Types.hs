{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Lib.Physics.Types where

import Lib.Util
import Lib.World
import qualified Data.Array as A
import Data.Monoid

newtype Rotate a = Rotate a
  deriving (Show, Functor, Foldable, Num)

instance Applicative Rotate where
  pure = Rotate
  Rotate f <*> Rotate x = Rotate (f x)

data Pos a = Pos (World a) (Rotate a)
  deriving (Show, Functor)

place :: Lens' (Pos a) (World a)
place = lens (\(Pos p _) -> p) $ \(Pos _ r) p -> Pos p r
rot :: Lens' (Pos a) (Rotate a)
rot = lens (\(Pos _ r) -> r) $ \(Pos p _) r -> Pos p r

angle :: Lens' (Rotate a) a
angle = lens (\(Rotate a) -> a) $ \_ a -> Rotate a

instance Applicative Pos where
  pure s = Pos (pure s) (pure s)
  Pos f g <*> Pos p r = Pos (f <*> p) (g <*> r)

instance Foldable Pos where
  foldMap f (Pos p r) = foldMap f p <> foldMap f r

instance Num a => Num (Pos a) where
  (+) = liftA2 (+)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  fromInteger p = pure 0

instance Space Pos where
  basis = Pos (World x y z) (Rotate r) where
    x = Pos (World 1 0 0) (Rotate 0)
    y = Pos (World 0 1 0) (Rotate 0)
    z = Pos (World 0 0 1) (Rotate 0)
    r = Pos (World 0 0 0) (Rotate 1)

instance Arith Pos where
  scale = pure
  dot (Pos p1 r1) (Pos p2 r2) = dot p1 p2 + (r1*r2)^.angle

newtype Shape = Shape (S1 -> R)

instance Show Shape where
  show _ = "[Shape]"

data Object = Object {
  _shape :: Shape,
  _coord :: Pos R,
  _veloc :: Pos R,
  _rotAxis :: World R,
  _gravity :: World R,
  _massInv :: Pos R
} deriving Show

shape :: Lens' Object Shape
shape = lens _shape $ \c v -> c {_shape = v}
coord :: Lens' Object (Pos R)
coord = lens _coord $ \c v -> c {_coord = v}
veloc :: Lens' Object (Pos R)
veloc = lens _veloc $ \c v -> c {_veloc = v}
rotAxis :: Lens' Object (World R)
rotAxis = lens _rotAxis $ \c v -> c {_rotAxis = v}
gravity :: Lens' Object (World R)
gravity = lens _gravity $ \c v -> c {_gravity = v}
massInv :: Lens' Object (Pos R)
massInv = lens _massInv $ \c v -> c {_massInv = v}

static :: SimpleGetter Object Object
static = to $ (gravity .~ 0) . (massInv .~ 0)

type ObjIx = Int
type PhysWorld = A.Array ObjIx Object

circle :: R -> Shape
circle r = Shape $ \_ -> r

square :: R -> Shape
square r = Shape $ \a -> r / cos (fmod a (pi/2) - pi/4)

type Density = R

make :: Shape -> Density -> Pos R -> Pos R -> World R -> Object
make (Shape s) rho c v ra = let
    aN = fromIntegral angleCount
    r i = s (2*pi*i/aN)
    integrate :: Int -> R
    integrate e = 2*pi/aN * sum [ ds (r i) (r (i+1)) | i <- [0..aN-1] ] where
      ds r1 r2 = rr (2+e) / fa where
        fa = (2 + fromIntegral e) * (1 + fromIntegral e)
        rr x = sum [ r1^i * r2^(x-1-i) | i <- [0..x-1] ]
    mass = integrate 1 * rho  -- 1 * J = r^1
    inertia = integrate 3 * rho -- r^2 * J = r^3
    mi = Pos (scale (1/mass)) (Rotate (1/inertia))
    g = World 0 1 0
  in Object (Shape s) c v ra g mi

fitO :: Object -> Object
fitO o = let
    p = fitP $ o^.coord.place
    v = fitV p $ o^.veloc.place
    ra = fitR p $ o^.rotAxis
  in o
    & coord.place .~ p
    & veloc.place .~ v
    & rotAxis .~ ra

applyGravity :: R -> Object -> Object
applyGravity dt o = o & veloc.place +~ g * scale dt where
  perpTo v p = let
      n = normal p
    in v - n * scale (dot n v)
  g = (o^.gravity) `perpTo` (o^.coord.place)

applyVelocity :: R -> Object -> Object
applyVelocity dt o = o & coord +~ o^.veloc * scale dt & fitO

data Local a = Local a a
  deriving (Show, Functor, Foldable)

instance V1 (Local a) a where
  x = lens (\(Local x _) -> x) $ \(Local _ y) x -> Local x y
instance V2 (Local a) a where
  y = lens (\(Local _ y) -> y) $ \(Local x _) y -> Local x y

instance Applicative Local where
  pure s = Local s s
  Local f g <*> Local x y = Local (f x) (g y)

instance Num a => Num (Local a) where
  (+) = liftA2 (+)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  fromInteger p = pure 0

instance Space Local where
  basis = Local (Local 1 0) (Local 0 1)

instance Arith Local where
  scale = pure
  dot (Local x1 y1) (Local x2 y2) = x1*x2 + y1*y2

type Constraint = () -- TODO
