{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE OverloadedStrings #-}

module Lib.Constraint where

import Lib.Util
import Lib.Object
import Lib.World

-- Local

data Local a = Local !a !a
  deriving (Show, Functor, Foldable)

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

instance V1 (Local a) a where
  x = lens (\(Local x _) -> x) $ \(Local _ y) x -> Local x y
instance V2 (Local a) a where
  y = lens (\(Local _ y) -> y) $ \(Local x _) y -> Local x y

toLocal :: Field a => Vertex a -> Local a
toLocal v = Local lx ly where
  l = v^.axisPos.whole * v^.axisPos.ratio
  a = v^.anglePos.angle
  lx = l * cos a
  ly = l * sin a

-- ContactPoint

data ContactPoint = ContactPoint {
  _world1 :: !(World R),
  _world2 :: !(World R),
  _contact1 :: !(Local R),
  _contact2 :: !(Local R),
  _direction1 :: !(World R),
  _direction2 :: !(World R),
  _flipped1 :: !Bool,
  _flipped2 :: !Bool
} deriving Show

world1 :: Lens' ContactPoint (World R)
world1 = lens _world1 $ \c v -> c {_world1 = v}
world2 :: Lens' ContactPoint (World R)
world2 = lens _world2 $ \c v -> c {_world2 = v}
contact1 :: Lens' ContactPoint (Local R)
contact1 = lens _contact1 $ \c v -> c {_contact1 = v}
contact2 :: Lens' ContactPoint (Local R)
contact2 = lens _contact2 $ \c v -> c {_contact2 = v}
direction1 :: Lens' ContactPoint (World R)
direction1 = lens _direction1 $ \c v -> c {_direction1 = v}
direction2 :: Lens' ContactPoint (World R)
direction2 = lens _direction2 $ \c v -> c {_direction2 = v}
flipped1 :: Lens' ContactPoint Bool
flipped1 = lens _flipped1 $ \c v -> c {_flipped1 = v}
flipped2 :: Lens' ContactPoint Bool
flipped2 = lens _flipped2 $ \c v -> c {_flipped2 = v}

instance FromAny ContactPoint where
  fromAny a = ContactPoint
    <$> (World
      <$> get a "w1x"
      <*> get a "w1y"
      <*> get a "w1z")
    <*> (World
      <$> get a "w2x"
      <*> get a "w2y"
      <*> get a "w2z")
    <*> (Local
      <$> get a "c1x"
      <*> get a "c1y")
    <*> (Local
      <$> get a "c2x"
      <*> get a "c2y")
    <*> (World
      <$> get a "d1x"
      <*> get a "d1y"
      <*> get a "d1z")
    <*> (World
      <$> get a "d2x"
      <*> get a "d2y"
      <*> get a "d2z")
    <*> get a "flipped1"
    <*> get a "flipped2"

-- Constraint

data Constraint = Constraint {
  _index1 :: !Int,
  _index2 :: !Int,
  _J1 :: !(Pos R),
  _J2 :: !(Pos R),
  _depth :: R,
  _positiveClamp :: Bool
} deriving Show

index1 :: Lens' Constraint Int
index1 = lens _index1 $ \c v -> c {_index1 = v}
index2 :: Lens' Constraint Int
index2 = lens _index2 $ \c v -> c {_index2 = v}
j1 :: Lens' Constraint (Pos R)
j1 = lens _J1 $ \c v -> c {_J1 = v}
j2 :: Lens' Constraint (Pos R)
j2 = lens _J2 $ \c v -> c {_J2 = v}
depth :: Lens' Constraint R
depth = lens _depth $ \c v -> c {_depth = v}
positiveClamp :: Lens' Constraint Bool
positiveClamp = lens _positiveClamp $ \c v -> c {_positiveClamp = v}

jv :: Constraint -> Pos R -> Pos R -> R
jv c v1 v2 = dot v1 (c^.j1) - dot v2 (c^.j2)
