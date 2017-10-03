{-# LANGUAGE OverloadedStrings #-}

module Lib.Physics.Types where

import Lib.Util
import qualified Data.Array as A
import Haste.Foreign

class V2 a where
  x :: Lens' a R
  y :: Lens' a R

class Arith a where
  scale :: R -> a
  dot :: a -> R

data Coord = Coord {
  _xC :: R,
  _yC :: R,
  _tC :: R
} deriving Show

instance V2 Coord where
  x = lens _xC $ \c v -> c {_xC = v}
  y = lens _yC $ \c v -> c {_yC = v}

t :: Lens' Coord R
t = lens _tC $ \c v -> c {_tC = v}

instance Num Coord where
  Coord x1 y1 t1 + Coord x2 y2 t2 = Coord (x1+x2) (y1+y2) (t1+t2)
  Coord x1 y1 t1 - Coord x2 y2 t2 = Coord (x1-x2) (y1-y2) (t1-t2)
  Coord x1 y1 t1 * Coord x2 y2 t2 = Coord (x1*x2) (y1*y2) (t1*t2)
  negate (Coord x y t) = Coord (-x) (-y) (-t)
  abs (Coord x y t) = Coord x y t
  signum _ = Coord 1 1 1
  fromInteger _ = Coord 0 0 0

instance Arith Coord where
  scale x = Coord x x x
  dot (Coord x y t) = x + y + t

data Local = Local {
  _xL :: R,
  _yL :: R
} deriving Show

instance V2 Local where
  x = lens _xL $ \c v -> c {_xL = v}
  y = lens _yL $ \c v -> c {_yL = v}

instance Num Local where
  Local x1 y1 + Local x2 y2 = Local (x1+x2) (y1+y2)
  Local x1 y1 - Local x2 y2 = Local (x1-x2) (y1-y2)
  Local x1 y1 * Local x2 y2 = Local (x1*x2) (y1*y2)
  negate (Local x y) = Local (-x) (-y)
  abs (Local x y) = Local (abs x) (abs y)
  signum (Local x y) = Local (signum x) (signum y)
  fromInteger _ = Local 0 0

instance Arith Local where
  scale x = Local x x
  dot (Local x y) = x + y

instance FromAny Local where
  fromAny a = Local
    <$> get a "x"
    <*> get a "y"

cross :: Local -> Local -> R
cross (Local x1 y1) (Local x2 y2) = x1*y2 - x2*y1

perp :: Local -> Local
perp (Local x y) = Local (-y) x

mix :: Local -> Local -> R -> R -> Local
mix (Local x1 y1) (Local x2 y2) r1 r2 = Local x y where
  x = (x1*r1 + x2*r2) / (r1+r2)
  y = (y1*r1 + y2*r2) / (r1+r2)

norm :: Local -> R
norm (Local x y) = sqrt $ x*x+y*y

normalize :: Local -> Local
normalize (Local x y) = let
    d = sqrt $ x*x+y*y
  in if d == 0 then Local 1 0 else Local (x/d) (y/d)

rotate :: R -> Local -> Local
rotate t (Local x y) = Local x' y' where
  x' = x*cos t - y*sin t
  y' = x*sin t + y*cos t

clamp :: (R,R) -> R -> R
clamp (i,a) x = min a $ max i x

data Shape = Circle R | Rect R R deriving Show

data Object = Object {
  _shape :: Shape,
  _coord :: Coord,
  _veloc :: Coord,
  _gravity :: Coord,
  _massInv :: Coord
} deriving Show

shape :: Lens' Object Shape
shape = lens _shape $ \c v -> c {_shape = v}
coord :: Lens' Object Coord
coord = lens _coord $ \c v -> c {_coord = v}
veloc :: Lens' Object Coord
veloc = lens _veloc $ \c v -> c {_veloc = v}
gravity :: Lens' Object Coord
gravity = lens _gravity $ \c v -> c {_gravity = v}
massInv :: Lens' Object Coord
massInv = lens _massInv $ \c v -> c {_massInv = v}

makeStatic :: Object -> Object
makeStatic o = o & gravity .~ 0 & massInv .~ 0

circle :: R -> R -> R -> Density -> Object
circle x y r rho = let
    s = Circle r
    m = pi*r^2*rho
    i = 1/2*pi*r^4*rho
    g = Coord 0 1 0
    mi = Coord (1/m) (1/m) (1/i)
  in Object s (Coord x y (pi/2)) 0 g mi

rect :: R -> R -> R -> R -> Density -> Object
rect x y w h rho = let
    s = Rect w h
    m = w*h*rho
    i = 1/12*(w*h^3+h*w^3)*rho
    g = Coord 0 1 0
    mi = Coord (1/m) (1/m) (1/i)
  in Object s (Coord x y (pi/2)) 0 g mi

type ObjIx = Int
type World = A.Array ObjIx Object

class HasDepth a where
  depth :: Lens' a R

data Constraint = Constraint {
  _o1 :: ObjIx,
  _o2 :: ObjIx,
  _j1 :: Coord,
  _j2 :: Coord,
  _depthC :: R
} deriving Show

o1 :: Lens' Constraint ObjIx
o1 = lens _o1 $ \c v -> c {_o1 = v}
o2 :: Lens' Constraint ObjIx
o2 = lens _o2 $ \c v -> c {_o2 = v}
j1 :: Lens' Constraint Coord
j1 = lens _j1 $ \c v -> c {_j1 = v}
j2 :: Lens' Constraint Coord
j2 = lens _j2 $ \c v -> c {_j2 = v}

instance HasDepth Constraint where
  depth = lens _depthC $ \c v -> c {_depthC = v}

data ContactPoint = ContactPoint {
  _local1 :: Local,
  _local2 :: Local,
  _normal1 :: Local,
  _normal2 :: Local,
  _depthP :: R
} deriving Show

local1 :: Lens' ContactPoint Local
local1 = lens _local1 $ \c v -> c {_local1 = v}
local2 :: Lens' ContactPoint Local
local2 = lens _local2 $ \c v -> c {_local2 = v}
normal1 :: Lens' ContactPoint Local
normal1 = lens _normal1 $ \c v -> c {_normal1 = v}
normal2 :: Lens' ContactPoint Local
normal2 = lens _normal2 $ \c v -> c {_normal2 = v}

instance HasDepth ContactPoint where
  depth = lens _depthP $ \c v -> c {_depthP = v}

jv :: Constraint -> Coord -> Coord -> R
jv c v1 v2 = dot (v1 * c^.j1) - dot (v2 * c^.j2)

normalizeCoord :: Coord -> Coord
normalizeCoord c@(Coord x y t) = Coord x' y' t' where
  y' = fmod y scrH
  x' = fmod x scrW
  t' = t

moveCoord :: (Int, Int) -> Coord -> Coord
moveCoord (i,j) c = let
    sc = Coord (fromIntegral i*scrW) (fromIntegral j*scrH) 0
  in c + sc

flipVeloc :: (Int, Int) -> Coord -> Coord
flipVeloc (i,j) = id

flipLocal :: (Int, Int) -> Local -> Local
flipLocal (i,j) = id

normalizeObject :: Object -> Object
normalizeObject o = o' where
  coord' = normalizeCoord $ o^.coord
  difx = round $ (coord'^.x - o^.coord.x) / scrW
  dify = round $ (coord'^.y - o^.coord.y) / scrH
  veloc' = flipVeloc (difx,dify) $ o^.veloc
  gravity' = flipVeloc (difx,dify) $ o^.gravity
  o' = Object (o^.shape) coord' veloc' gravity' (o^.massInv)
