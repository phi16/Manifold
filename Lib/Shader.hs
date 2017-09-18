{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFoldable #-}

module Lib.Shader (fieldStr, gradStr) where

import Lib.Util hiding ((++), concat)
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
  abs x = C ["abs(",x,")"]
  signum x = C ["sign(",x,")"]
  fromInteger p = S $ show p ++ "."

instance Fractional (Var String) where
  x / y = C ["(",x,")/(",y,")"]
  recip x = C ["1./(",x,")"]
  fromRational p = S $ show (fromRational p :: Double)

instance Floating (Var String) where
  pi = "pi"
  exp x = C ["exp(",x,")"]
  log x = C ["log(",x,")"]
  sqrt x = C ["sqrt(",x,")"]
  x ** y = C ["pow(",x,",",y,")"]
  logBase b x = C ["log(",x,")/log(",b,")"]
  sin x = C ["sin(",x,")"]
  cos x = C ["cos(",x,")"]
  tan x = C ["tan(",x,")"]
  asin x = C ["asin(",x,")"]
  acos x = C ["acos(",x,")"]
  atan x = C ["atan(",x,")"]
  sinh x = C ["sinh(",x,")"]
  cosh x = C ["cosh(",x,")"]
  tanh x = C ["tanh(",x,")"]
  asinh x = C ["asinh(",x,")"]
  acosh x = C ["acosh(",x,")"]
  atanh x = C ["atanh(",x,")"]

instance Eq (Var String) where
  (==) = error "(==) is not defined"
  (/=) = error "(/=) is not defined"

instance Ord (Var String) where
  (<) = error "(<) is not defined"
  (>) = error "(>) is not defined"
  (<=) = error "(<=) is not defined"
  (>=) = error "(>=) is not defined"
  compare = error "compare is not defined"
  min x y = C ["min(",x,",",y,")"]
  max x y = C ["max(",x,",",y,")"]

argument :: World (Var String)
argument = fmap S $ World "x" "y" "z"

fieldStr :: JSString
fieldStr = toJSStr $ fold $ field argument

gradStr :: JSString
gradStr = toJSStr $ let
    g = gradient argument
    gs = C $ intersperse "," $ toList g
  in fold $ C $ ["vec3(",gs,")"]
