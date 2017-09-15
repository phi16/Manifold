{-# LANGUAGE PackageImports #-}

module Main where

import Lib.Util hiding (length)
import Lib.Screen
import Lib.Render
import Lib.World
import Lib.Physics
import Data.Traversable
import qualified "mtl" Control.Monad.State as S
import Data.Array

main :: IO ()
main = do
  compile fieldStr gradStr
  i <- initial
  run i step

type State = PhysWorld

initial :: IO State
initial = do
  let
    ra = World 0 0 1
    p1 = World (-0.8) 0.5 0
    p2 = World 1.3 0 0
    v1 = World (-0.2) 0 1
    v2 = World 0 (-0.1) 0.3
    o1 = make (circle 0.04) 1.2 (Pos p1 0) (Pos v1 0) ra
    o2 = make (square 0.04) 1.2 (Pos p2 0) (Pos v2 3) ra
    ls = [o1,o2]
  return $ listArray (0,length ls-1) ls

step :: State -> IO State
step w = do
  refresh
  draw
  for w drawObject
  S.execStateT nextFrame w
