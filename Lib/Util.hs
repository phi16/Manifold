{-# LANGUAGE OverloadedStrings #-}

module Lib.Util (
  module Control.Monad,
  module Lens.Micro,
  module Lens.Micro.GHC,
  module Lens.Micro.Mtl,
  R, Density,
  (+~), (*~), fmod,
  scrW, scrH, refresh,
  drawCircle, draw,
  io,
  run
) where

import Haste
import Haste.Concurrent
import Haste.Foreign
import Haste.Graphics.AnimationFrame
import Control.Monad
import Control.Monad.IO.Class
import Lens.Micro
import Lens.Micro.GHC
import Lens.Micro.Mtl

type R = Double
type Density = R

(+~) :: Num a => ASetter s s a a -> a -> s -> s
l +~ x = l %~ (+x)
infix 4 +~

(*~) :: Num a => ASetter s s a a -> a -> s -> s
l *~ x = l %~ (*x)
infix 4 *~

fmod :: RealFrac a => a -> a -> a
fmod e m = e + (-1) * fromIntegral (floor (e/m)) * m

scrW :: R
scrW = constant "scrW"
scrH :: R
scrH = constant "scrH"
refresh :: IO ()
refresh = ffi "refresh"
drawCircle :: R -> R -> R -> R -> IO ()
drawCircle = ffi "drawCircle"
draw :: IO ()
draw = ffi "draw"

io :: MonadIO m => IO a -> m a
io = liftIO

frameStep :: CIO ()
frameStep = do
  v <- newEmptyMVar
  liftIO $ requestAnimationFrame $ const $ concurrent $ putMVar v ()
  takeMVar v

run :: a -> (a -> IO a) -> IO ()
run initial step = concurrent $ do
  stepper <- statefully initial (\s _ -> io $ Just <$> step s)
  forever $ do
    stepper ! ()
    frameStep
