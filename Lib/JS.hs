{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFoldable #-}

module Lib.JS (boundJSStr, boundGradJSStr) where

import Lib.Util
import Lib.World
import Haste
import Haste.Prim
import Data.List
import Data.String
import Data.Foldable

data Var s = S s | C [Var s]
  deriving Foldable

instance IsString (Var String) where
  fromString = S

instance Num (Var String) where
  x + y = C ["(",x,")+(",y,")"]
  x * y = C ["(",x,")*(",y,")"]
  negate x = C ["-(",x,")"]
  abs x = C ["Math.abs(",x,")"]
  signum x = C ["Math.sign(",x,")"]
  fromInteger p = S $ show p ++ "."

instance Fractional (Var String) where
  x / y = C ["(",x,")/(",y,")"]
  recip x = C ["1/(",x,")"]
  fromRational p = S $ show (fromRational p :: Double)

instance Floating (Var String) where
  pi = "Math.PI"
  exp x = C ["Math.exp(",x,")"]
  log x = C ["Math.log(",x,")"]
  sqrt x = C ["Math.sqrt(",x,")"]
  x ** y = C ["Math.pow(",x,",",y,")"]
  logBase b x = C ["Math.log(",x,")/Math.log(",b,")"]
  sin x = C ["Math.sin(",x,")"]
  cos x = C ["Math.cos(",x,")"]
  tan x = C ["Math.tan(",x,")"]
  asin x = C ["Math.asin(",x,")"]
  acos x = C ["Math.acos(",x,")"]
  atan x = C ["Math.atan(",x,")"]
  sinh x = C ["Math.sinh(",x,")"]
  cosh x = C ["Math.cosh(",x,")"]
  tanh x = C ["Math.tanh(",x,")"]
  asinh x = C ["Math.asinh(",x,")"]
  acosh x = C ["Math.acosh(",x,")"]
  atanh x = C ["Math.atanh(",x,")"]

instance Eq (Var String) where
  (==) = error "(==) is not defined"
  (/=) = error "(/=) is not defined"

instance Ord (Var String) where
  (<) = error "(<) is not defined"
  (>) = error "(>) is not defined"
  (<=) = error "(<=) is not defined"
  (>=) = error "(>=) is not defined"
  compare = error "compare is not defined"
  min x y = C ["Math.min(",x,",",y,")"]
  max x y = C ["Math.max(",x,",",y,")"]

argument :: World (Var String)
argument = fmap S $ World "x" "y" "z"

boundJSStr :: JSString
boundJSStr = toJSStr $ fold $ boundary argument

boundGradJSStr :: JSString
boundGradJSStr = toJSStr $ let
    g = boundGradient argument
  in fold $ C $ ["({x:",g^.x,",y:",g^.y,",z:",g^.z,"})"]
