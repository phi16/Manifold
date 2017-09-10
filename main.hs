{-# LANGUAGE PackageImports #-}

module Main where

import Prelude hiding (length)
import Lib.Util
import Lib.World
import Lib.Screen
import Lib.Render
import Lib.AD
import qualified "mtl" Control.Monad.State as S

main :: IO ()
main = do
  compile fieldStr gradStr
  i <- initial
  run i step

type State = (World R, World R, World R)

initial :: IO State
initial = return (World (-1.3) 0 0, normalize $ World 0 1 0.2, World 0 0 1)
-- initial = return (World (-1) 0 0, normalize $ World 0 (-1) 1, World 0 0 1)

step :: State -> IO State
step v@(coord@(World x y z), veloc, rotAx@(World rx ry rz)) = do
  refresh
  draw x y z rx ry rz
  let
    dt = 0.02
    pos = coord + veloc * scale dt
    difPos = distance pos
    coord' = pos - scale difPos * normal pos
    gradP' = normal coord'
    velDir = normalize veloc
    velLen = length veloc
    adjV = - dot veloc gradP'
    velDir' = veloc + gradP' * scale adjV
    veloc' = scale velLen * normalize velDir'
    adjR = - dot rotAx gradP'
    rotAx' = normalize $ rotAx + gradP' * scale adjR
  return (coord', veloc', rotAx')
