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
  Expr x x' / Expr y y' = Expr (x/y) (liftA2 (\x' y' -> (x'*y-x*y')/y^2) x' y')
  recip (Expr x x') = Expr (1/x) (fmap (*(-1/x^2)) x')
  fromRational p = Expr (fromRational p) (pure 0)

instance Linear f a => Floating (Expr f a) where
  pi = Expr pi (pure 0)
  exp (Expr x x') = Expr (exp x) (fmap (*(exp x)) x')
  log (Expr x x') = Expr (log x) (fmap (*(1/x)) x')
  sqrt (Expr x x') = Expr (sqrt x) (fmap (*(1/2/sqrt x)) x')
  Expr x x' ** Expr y y' = Expr (x**y) (liftA2 (\x' y' -> x**y*(y*x'/x+y'*log x)) x' y')
  logBase b x = log x / log b
  sin (Expr x x') = Expr (sin x) (fmap (*(cos x)) x')
  cos (Expr x x') = Expr (cos x) (fmap (*(-sin x)) x')
  tan (Expr x x') = Expr (tan x) (fmap (/((cos x)^2)) x')
  asin (Expr x x') = Expr (asin x) (fmap (/(sqrt (1-x^2))) x')
  acos (Expr x x') = Expr (acos x) (fmap (/(-sqrt (1-x^2))) x')
  atan (Expr x x') = Expr (atan x) (fmap (/(1+x^2)) x')
  sinh (Expr x x') = Expr (sinh x) (fmap (*(cosh x)) x')
  cosh (Expr x x') = Expr (cosh x) (fmap (*(sinh x)) x')
  tanh (Expr x x') = Expr (tanh x) (fmap (/((cosh x)^2)) x')
  asinh (Expr x x') = Expr (asinh x) (fmap (/(sqrt (x^2+1))) x')
  acosh (Expr x x') = Expr (acosh x) (fmap (/(sqrt (x^2-1))) x')
  atanh (Expr x x') = Expr (atanh x) (fmap (/(1-x^2)) x')

instance Linear f a => Eq (Expr f a) where
  (==) = error "(==) is not defined"
  (/=) = error "(/=) is not defined"

instance Linear f a => Ord (Expr f a) where
  (<) = error "(<) is not defined"
  (>) = error "(>) is not defined"
  (<=) = error "(<=) is not defined"
  (>=) = error "(>=) is not defined"
  compare = error "compare is not defined"
  min (Expr x x') (Expr y y') = Expr (min x y) (liftA2 (\x' y' -> mix y' x' $ signum (y-x) * 0.5 + 0.5) x' y')
  max (Expr x x') (Expr y y') = Expr (max x y) (liftA2 (\x' y' -> mix x' y' $ signum (y-x) * 0.5 + 0.5) x' y')

grad :: Linear f a => (f (Expr f a) -> Expr f a) -> f a -> f a
grad f p = let
    Expr _ diff = f (liftA2 Expr p basis)
  in diff
