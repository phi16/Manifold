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

type State = (World R, World R)

initial :: IO State
initial = return (World (-1.3) 0 0, normalize $ World 0 1 0.2)

step :: State -> IO State
step v@(coord@(World x y z), veloc) = do
  refresh
  draw x y z
  let
    dt = 0.05
    pos = coord + veloc * scale dt
    difPos = distance pos
    coord' = pos - scale difPos * normal pos
    gradP' = normal coord'
    velDir = normalize veloc
    velLen = length veloc
    adj = - dot veloc gradP'
    velDir' = veloc + gradP' * scale adj
    veloc' = scale velLen * normalize velDir'
  return (coord', veloc')
