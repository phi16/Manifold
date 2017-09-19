{-# LANGUAGE OverloadedStrings #-}

module Lib.Screen where

import Lib.Util
import Haste
import Haste.Concurrent
import Haste.Foreign
import Haste.Graphics.AnimationFrame
import Control.Monad
import Control.Monad.IO.Class
import Data.IORef

scrW :: R
scrW = constant "scrW"
scrH :: R
scrH = constant "scrH"
refresh :: IO ()
refresh = ffi "refresh"
draw :: IO ()
draw = ffi "draw"
vertex :: R -> R -> R -> R -> R -> R -> IO ()
vertex = ffi "vertex"
drawTriangles :: IO ()
drawTriangles = ffi "drawTriangles"
compile :: JSString -> JSString -> IO ()
compile = ffi "compile"

frameStep :: CIO ()
frameStep = do
  v <- newEmptyMVar
  liftIO $ requestAnimationFrame $ const $ concurrent $ putMVar v ()
  takeMVar v

run :: a -> (a -> IO a) -> IO ()
run initial step = concurrent $ do
  sRef <- io $ newIORef initial
  forever $ do
    io $ do
      s <- readIORef sRef
      s' <- step s
      writeIORef sRef s'
    frameStep
