{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Lib.Physics (
  nextFrame
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
import Haste.Foreign (constant)

dt :: R
dt = 0.01

projective :: Bool
projective = constant "projective"

applyGravity :: Object -> Object
applyGravity o = o & veloc.place +~ g * scale dt where
  g = (o^.gravity) (o^.coord.place) `perpTo` (o^.surface)

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
      return $ cs >>= \(ContactPoint w1 w2 l1 l2 d1 d2 f1 f2) -> let
          v = w2 - w1
          d = length v
          n = v * scale (1/d)
          ln1 = normal w1
          ln2 = normal w2
          ff1 = if f1 then -1 else 1
          ff2 = if f2 then -1 else 1
          r1 = scale (length l1) * normalize d1
          r2 = scale (length l2) * normalize d2
          n1 = scale ff1 * n
          n2 = scale ff2 * n
        in if i1 /= i2
          then let
              j1 = Pos (n1`perpTo`ln1) (Rotate $ (cross n1 r1)`dot`ln1)
              j2 = Pos (n2`perpTo`ln2) (Rotate $ (cross n2 r2)`dot`ln2)
              c = Constraint i1 i2 j1 j2 d True
            in [c]
          else let
              j1 = Pos (n1`cross`ln1) (Rotate $ (cross (n1`cross`ln1) r1)`dot`ln1)
              j2 = Pos (n2`cross`ln2) (Rotate $ (cross (n2`cross`ln2) r2)`dot`ln2)
              c1 = Constraint i1 i2 j1 0 d False
              c2 = Constraint i1 i2 0 j2 d False
            in [c1,c2]

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
    valid = not (c^.positiveClamp) || ldt >= 0
  when (jmjt /= 0 && valid) $ do
    let sameScale = if c^.index1 == c^.index2 then 0.6 else 1
    ix (c^.index1).veloc += d1^.massInv * c^.j1 * scale (ldt * sameScale)
    ix (c^.index2).veloc -= d2^.massInv * c^.j2 * scale (ldt * sameScale)
