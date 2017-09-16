{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PackageImports #-}

module Lib.Physics (
  nextFrame,
  drawObject
) where

import Lib.Util
import Lib.World
import Lib.Object
import Lib.Constraint
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

collide :: Object -> Object -> [ContactPoint]
collide o1 o2 = []

generateConstraints :: S.StateT PhysWorld IO [Constraint]
generateConstraints = do
  (s,f) <- use $ to A.bounds
  fmap concat $ for [s..f] $ \i1 -> do
    fmap concat $ for [i1..f] $ \i2 -> do
      Just o1 <- preuse $ ix i1
      Just o2 <- preuse $ ix i2
      for (collide o1 o2) $ \(ContactPoint l1 l2 n1 n2 d) -> do
        return undefined

solveConstraints :: [Constraint] -> S.StateT PhysWorld IO ()
solveConstraints cs = return ()
