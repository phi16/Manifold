{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}

module Lib.Constraint where

import Lib.Util
import Lib.Object
import Lib.World

-- Local

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

-- ContactPoint

data ContactPoint = ContactPoint {
  _local1 :: Vertex R,
  _local2 :: Vertex R,
  _normal1 :: World R,
  _normal2 :: World R,
  _depth :: R
} deriving Show

-- Constraint

type Constraint = () -- TODO
