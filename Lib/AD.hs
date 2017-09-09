{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}

module Lib.AD where

import Lib.Util

data Expr f a = Expr a (f a)

instance Linear f a => Num (Expr f a) where
  Expr x x' + Expr y y' = Expr (x+y) (liftA2 (+) x' y')
  Expr x x' * Expr y y' = Expr (x*y) (liftA2 (\x' y' -> x*y'+x'*y) x' y')
  negate (Expr x x') = Expr (-x) (fmap negate x')
  abs (Expr x x') = Expr (abs x) (fmap (*signum x) x')
  signum (Expr x x') = Expr (signum x) (pure 0)
  fromInteger p = Expr (fromInteger p) (pure 0)

instance Linear f a => Fractional (Expr f a) where
  Expr x x' / Expr y y' = Expr (x/y) undefined
  recip (Expr x x') = Expr (1/x) undefined
  fromRational p = Expr (fromRational p) (pure 0)

instance Linear f a => Floating (Expr f a) where
  sqrt (Expr x x') = Expr (sqrt x) (fmap (*(1/2/sqrt x)) x')

grad :: Linear f a => (f (Expr f a) -> Expr f a) -> f a -> f a
grad f p = let
    Expr _ diff = f (liftA2 Expr p basis)
  in diff
