{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFoldable #-}

module Lib.Render (fieldStr, gradStr) where

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
  abs x = C ["abs(",x,")"]
  signum x = C ["sign(",x,")"]
  fromInteger p = S $ show p ++ "."

instance Fractional (Var String) where
  x / y = C ["(",x,")/(",y,")"]
  recip x = C ["1./(",x,")"]
  fromRational p = S $ show (fromRational p :: Double)

instance Floating (Var String) where
  sqrt x = C ["sqrt(",x,")"]

argument :: World (Var String)
argument = World (S "x") (S "y") (S "z")

fieldStr :: JSString
fieldStr = toJSStr $ fold $ field argument

gradStr :: JSString
gradStr = toJSStr $ let
    World x y z = gradient argument
  in fold $ C ["vec3(",x,",",y,",",z,")"]
