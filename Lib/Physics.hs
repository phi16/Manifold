{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TupleSections #-}

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
import Debug.Trace

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
collide o1 o2 = let
    coordOf :: (Show a, Field a) => World a -> [Polygon a] -> Maybe (Local a)
    coordOf p ss = asum $ ss <&> \s -> do
      let
        wp1 = s^.x.worldPos
        wp2 = s^.y.worldPos
        wp3 = s^.z.worldPos
        n = normalize $ cross (wp3-wp1) (wp3-wp2)
        dp = dot (p - wp1) n
      guard $ abs dp < 0.1
      let
        pp = p - n * scale dp -- on the polygon
        lineDist l0 l1 l2 = let
            nl = normalize $ cross n (l2-l1)
          in dot (pp - l1) nl / dot (l0 - l1) nl
        d1 = lineDist wp1 wp2 wp3
        d2 = lineDist wp2 wp3 wp1
        d3 = lineDist wp3 wp1 wp2
      guard $ all (>=0) [d1,d2,d3]
      -- guard $ d1+d2+d3 == 1
      let
        lo1 = toLocal $ s^.x
        lo2 = toLocal $ s^.y
        lo3 = toLocal $ s^.z
      return $ lo1*scale d1 + lo2*scale d2 + lo3*scale d3
    intersect :: Object -> [Polygon R] -> [(World R, Local R)]
    intersect frame target = catMaybes $ frame^..outline.each.to localize where
      localize v = do
        l <- coordOf (v^.worldPos) target
        let l' = toLocal v
        guard $ length (l - l') >= 0.0001
        return (v^.worldPos, l)
    sect1 = intersect o1 $ o2^.polygon
    sect2 = intersect o2 $ o1^.polygon
  in L.length (show (sect1,sect2)) `seq` []

generateConstraints :: S.StateT PhysWorld IO [Constraint]
generateConstraints = do
  (s,f) <- use $ to A.bounds
  fmap concat $ for [s..f] $ \i1 -> do
    fmap concat $ for [i1..f] $ \i2 -> do
      Just o1 <- preuse $ ix i1
      Just o2 <- preuse $ ix i2
      for (collide o1 o2) $ \(ContactPoint c1 c2 n1 n2) -> do
        return ()

solveConstraints :: [Constraint] -> S.StateT PhysWorld IO ()
solveConstraints cs = return ()
