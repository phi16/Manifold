{-# LANGUAGE OverloadedStrings #-}

module Lib.Screen where

import Lib.Util
import Haste
import Haste.Concurrent
import Haste.Foreign
import Haste.Graphics.AnimationFrame
import Control.Monad
import Control.Monad.IO.Class

scrW :: R
scrW = constant "scrW"
scrH :: R
scrH = constant "scrH"
refresh :: IO ()
refresh = ffi "refresh"
draw :: R -> R -> R -> R -> R -> R -> IO ()
draw = ffi "draw"
compile :: JSString -> JSString -> IO ()
compile = ffi "compile"

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
