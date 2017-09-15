{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PackageImports #-}

module Lib.Physics (
  module Lib.Physics.Types,
  nextFrame,
  drawObject
) where

import Lib.Util
import Lib.World
import Lib.Physics.Types
import Data.Traversable
import Lib.Screen
import qualified "mtl" Control.Monad.State as S

dt :: R
dt = 0.05

nextFrame :: S.StateT PhysWorld IO ()
nextFrame = do
  traverse %= applyGravity dt
  cs <- generateConstraints
  solveConstraints cs
  traverse %= applyVelocity dt
  return ()

generateConstraints :: S.StateT PhysWorld IO [Constraint]
generateConstraints = return []

solveConstraints :: [Constraint] -> S.StateT PhysWorld IO ()
solveConstraints cs = return ()

drawObject :: Object -> IO ()
drawObject o = do
  let
    c = o^.coord.place
    ra = o^.rotAxis
    Shape sf = o^.shape

    ax = ra
    ay = cross ra (normal c)
    aC = fromIntegral angleCount
    pC = fromIntegral proceedCount
  pss' <- for [0..aC-1] $ \d -> do
    let
      a = d/aC*2*pi
      s = sf a
      a' = a + o^.coord.rot.angle
      dir = ax * scale (cos a') + ay * scale (sin a')
    S.evalStateT ?? (c,dir) $ do
      for [1..pC] $ \i -> do
        v <- use _2
        _1 += v * scale ((1 + 1 / i) * s) -- TODO
        _1 %= fitP
        p <- use _1
        _2 %= fitR p
        use _1
  let
    comp :: [World R] -> [World R] -> [(World R, World R, World R)]
    comp xs ys = let
        make :: (World R, World R) -> (World R, World R) -> [(World R, World R, World R)]
        make (a,b) (c,d) = [(a,b,c),(b,c,d)]
        rects = zipWith make (zip xs $ tail xs) (zip ys $ tail ys)
      in (c,head xs,head ys) : concat rects
    pss = concat $ zipWith comp pss' (tail $ pss' ++ [head pss'])
  -- TODO : reuse
  for pss $ \(World x1 y1 z1, World x2 y2 z2, World x3 y3 z3) ->
    triangle x1 y1 z1 x2 y2 z2 x3 y3 z3
  drawTriangles
