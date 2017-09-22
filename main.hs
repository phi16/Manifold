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
    p1 = World 0.4 0.4 0.4
    p2 = World 1.3 0 0
    p3 = World 1 1 0
    p4 = World 0 1 1
    o1 = make (circle 0.4) 1.2 (Pos p1 0) 0 ra
    o2 = make (circle 0.4) 1.2 (Pos p2 0) 0 ra
    o3 = make (circle 0.4) 1.2 (Pos p3 0) 0 ra
    o4 = make (circle 0.4) 1.2 (Pos p4 0) 0 ra
    ls = [o1,o2,o3,o4]
  return $ listArray (0,length ls-1) ls

step :: State -> IO State
step w = do
  refresh
  draw
  let (s,f) = bounds w
  for [s..f] $ \i -> passObject i $ w^?!ix i
  drawObjects
  S.execStateT nextFrame w
