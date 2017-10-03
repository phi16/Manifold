{-# LANGUAGE PackageImports #-}

module Main where

import Lib.Util
import Lib.Physics
import qualified Data.Array as A
import qualified "mtl" Control.Monad.State as S
import Data.Traversable

main :: IO ()
main = run initial step

showObject' :: Object -> IO ()
showObject' o = case o^.shape of
  Circle r -> drawCircle (o^.coord.x) (o^.coord.y) (o^.coord.t) r
  Rect w h -> drawRect (o^.coord.x) (o^.coord.y) (o^.coord.t) w h

showObject :: Object -> IO ()
showObject o = void $ do
  for [-1..1] $ \i -> do
    for [-1..1] $ \j -> do
      showObject' $ o & coord %~ moveCoord (i,j)

type State = World

initial :: State
initial = let
    c4 = circle (scrW/2-2) 60 80 1
    c5 = circle (scrW/2-1) 80 80 1
    c6 = circle (scrW/2-3) 100 80 1
  in A.listArray (0,2) [c4,c5,c6]

step :: State -> IO State
step v = do
  refresh
  for v showObject
  v' <- S.execStateT nextFrame v
  return v'
