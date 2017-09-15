{-# LANGUAGE PackageImports #-}

module Main where

import Prelude hiding (length)
import Lib.Util
import Lib.Screen
import Lib.Render
import Lib.Physics
import qualified "mtl" Control.Monad.State as S

main :: IO ()
main = do
  compile fieldStr gradStr
  i <- initial
  run i step

type State = (World R, World R, World R)

initial :: IO State
-- initial = return (World (-1) 0 0, normalize $ World 0 (-1) 1, World 0 0 1)
initial = return (World (-1.3) 0 0, normalize $ World 0 1 0.2, World 0 0 1)

step :: State -> IO State
step v@(coord@(World x y z), veloc, rotAx@(World rx ry rz)) = do
  refresh
  draw x y z rx ry rz
  let
    ax = rotAx
    ay = cross rotAx (normal coord)
    u = angleCount
  pss' <- for [0..u-1] $ \d -> do
    let
      angle = d/u*2*pi
      s = 1 / cos (fmod angle (pi/2) - pi/4)
      dir = ax * scale (cos angle) + ay * scale (sin angle)
    S.evalStateT ?? (coord,dir) $ do
      for [1..proceedCount] $ \i -> do
        v <- use _2
        _1 += v * scale (0.055 * (1 + 1 / i) * s)
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
      in (coord,head xs,head ys) : concat rects
    pss = concat $ zipWith comp pss' (tail $ pss' ++ [head pss'])
  for pss $ \(World x1 y1 z1, World x2 y2 z2, World x3 y3 z3) ->
    triangle x1 y1 z1 x2 y2 z2 x3 y3 z3
  drawTriangles
  let
    dt = 0.02
    pos = coord + veloc * scale dt
    coord' = fitP pos
    veloc' = fitV coord' veloc
    rotAx' = fitR coord' rotAx
  return (coord', veloc', rotAx')
