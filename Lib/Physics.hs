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

generateConstraints :: S.StateT PhysWorld IO [Constraint]
generateConstraints = return []

solveConstraints :: [Constraint] -> S.StateT PhysWorld IO ()
solveConstraints cs = return ()
