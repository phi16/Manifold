{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Lib.Physics (
  nextFrame,
  drawObject
) where

import Prelude hiding (length)
import Lib.Util
import Lib.World
import Lib.Object
import Lib.Constraint
import Control.Applicative
import Control.Monad
import qualified Data.List as L
import Data.Maybe
import Data.Foldable hiding (length)
import Data.Traversable
import qualified Data.Array as A
import qualified "mtl" Control.Monad.State as S

dt :: R
dt = 0.05

applyGravity :: Object -> Object
applyGravity o = o & veloc.place +~ g * scale dt where
  g = (o^.gravity) `perpTo` (o^.surface)

applyVelocity :: Object -> Object
applyVelocity o = o & coord +~ o^.veloc * scale dt & fitO

nextFrame :: S.StateT PhysWorld IO ()
nextFrame = do
  traverse %= applyGravity
  cs <- generateConstraints
  solveConstraints cs
  traverse %= applyVelocity
  return ()

collide :: Object -> Object -> IO [ContactPoint]
collide = ffi "collide"

generateConstraints :: S.StateT PhysWorld IO [Constraint]
generateConstraints = do
  (s,f) <- use $ to A.bounds
  fmap concat $ for [s..f] $ \i1 -> do
    fmap concat $ for [i1..f] $ \i2 -> do
      Just o1 <- preuse $ ix i1
      Just o2 <- preuse $ ix i2
      cs <- io $ collide o1 o2
      for cs $ \(ContactPoint c1 c2 n1 n2) -> do
        return ()

solveConstraints :: [Constraint] -> S.StateT PhysWorld IO ()
solveConstraints cs = return ()
