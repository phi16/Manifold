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
dt = 0.01

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
      for cs $ \(ContactPoint w1 w2 l1 l2 d1 d2) -> do
        let
          v = w2 - w1
          d = length v
          n = v * scale (1/d)
          n1 = normal w1
          n2 = normal w2
          r1 = scale (length l1) * normalize d1
          r2 = scale (length l2) * normalize d2
          j1 = Pos (n`perpTo`n1) (Rotate $ length (cross r1 n))
          j2 = Pos (n`perpTo`n2) (Rotate $ length (cross r2 n))
        return $ Constraint i1 i2 j1 j2 d

solveConstraints :: [Constraint] -> S.StateT PhysWorld IO ()
solveConstraints cs = replicateM_ 5 $ for cs $ \c -> do
  Just d1 <- preuse $ ix (c^.index1)
  Just d2 <- preuse $ ix (c^.index2)
  let
    bias = 0.1 * c^.depth / dt
    jvt = jv c (d1^.veloc) (d2^.veloc)
    measure (Pos (World x y z) (Rotate a)) = x + y + z + a
    jmjt = measure (c^.j1 * d1^.massInv * c^.j1) + measure (c^.j2 * d2^.massInv * c^.j2)
    ldt = - (jvt - bias) / jmjt
  when (jmjt /= 0 && ldt >= 0) $ do
    let sameScale = if c^.index1 == c^.index2 then 0.6 else 1
    ix (c^.index1).veloc += d1^.massInv * c^.j1 * scale (ldt * sameScale)
    ix (c^.index2).veloc -= d2^.massInv * c^.j2 * scale (ldt * sameScale)
