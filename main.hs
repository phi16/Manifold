{-# LANGUAGE PackageImports #-}

module Main where

import Lib.Util hiding (length)
import Lib.Screen
import Lib.Shader
import Lib.World
import Lib.Object
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
    -- p1 = World (-0.8) 0.5 0 -- torus
    -- p2 = World 1.3 0 0
    -- v1 = World 0 0 0.3
    -- v2 = World 0 (-0.1) 0.3
    -- p1 = World 0 0.5 (-0.5) -- sphere
    -- p2 = World 0.4 0 0
    -- v1 = World 0 0 0.3
    -- v2 = World 0 (-0.1) 0.3
    p1 = World 0 0 2 -- plane
    p2 = World (0.1) 0 0
    v1 = World 0 0 0
    v2 = World 0 0 0
    o1 = make (square 0.2) 1.2 (Pos p1 (Rotate $ pi/4)) (Pos v1 0) ra
    o2 = make (square 0.2) 1.2 (Pos p2 (Rotate $ pi/4)) (Pos v2 0) ra ^. static
    ls = [o1,o2]
  return $ listArray (0,length ls-1) ls

step :: State -> IO State
step w = do
  refresh
  draw
  for w drawObject
  S.execStateT nextFrame w
