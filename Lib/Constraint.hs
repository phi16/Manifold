{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}

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
  _contact1 :: !(Local R),
  _contact2 :: !(Local R),
  _normal1 :: !(World R),
  _normal2 :: !(World R)
} deriving Show

contact1 :: Lens' ContactPoint (Local R)
contact1 = lens _contact1 $ \c v -> c {_contact1 = v}
contact2 :: Lens' ContactPoint (Local R)
contact2 = lens _contact2 $ \c v -> c {_contact2 = v}
normal1 :: Lens' ContactPoint (World R)
normal1 = lens _normal1 $ \c v -> c {_normal1 = v}
normal2 :: Lens' ContactPoint (World R)
normal2 = lens _normal2 $ \c v -> c {_normal2 = v}

-- Constraint

type Constraint = () -- TODO
