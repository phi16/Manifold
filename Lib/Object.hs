{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Lib.Object where

import Lib.Util
import Lib.World
import Lib.Screen
import qualified Data.Array as A
import Data.Monoid
import Data.Foldable
import Data.Traversable
import qualified "mtl" Control.Monad.State as S

-- Rotate

newtype Rotate a = Rotate a
  deriving (Show, Functor, Foldable, Num)

instance Applicative Rotate where
  pure = Rotate
  Rotate f <*> Rotate x = Rotate (f x)

angle :: Lens' (Rotate a) a
angle = lens (\(Rotate a) -> a) $ \_ a -> Rotate a

-- Pos

data Pos a = Pos !(World a) !(Rotate a)
  deriving (Show, Functor)

place :: Lens' (Pos a) (World a)
place = lens (\(Pos p _) -> p) $ \(Pos _ r) p -> Pos p r
rot :: Lens' (Pos a) (Rotate a)
rot = lens (\(Pos _ r) -> r) $ \(Pos p _) r -> Pos p r

instance Applicative Pos where
  pure s = Pos (pure s) (pure s)
  Pos f g <*> Pos p r = Pos (f <*> p) (g <*> r)

instance Foldable Pos where
  foldMap f (Pos p r) = foldMap f p <> foldMap f r

instance Num a => Num (Pos a) where
  (+) = liftA2 (+)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  fromInteger p = pure 0

instance Space Pos where
  basis = Pos (World x y z) (Rotate r) where
    x = Pos (World 1 0 0) (Rotate 0)
    y = Pos (World 0 1 0) (Rotate 0)
    z = Pos (World 0 0 1) (Rotate 0)
    r = Pos (World 0 0 0) (Rotate 1)

instance Arith Pos where
  scale = pure
  dot (Pos p1 r1) (Pos p2 r2) = dot p1 p2 + (r1*r2)^.angle

-- Shape

newtype Shape = Shape (S1 -> R)

instance Show Shape where
  show _ = "[Shape]"

-- Ratio

data Ratio a = Ratio {
  _ratio :: !a,
  _whole :: !a
} deriving Show

ratio :: Lens' (Ratio a) a
ratio = lens _ratio $ \c v -> c {_ratio = v}
whole :: Lens' (Ratio a) a
whole = lens _whole $ \c v -> c {_whole = v}

-- Vertex

data Vertex a = Vertex {
  _worldPos :: !(World a),
  _axisPos :: !(Ratio a),
  _anglePos :: !(Rotate a),
  _direction :: !(World a)
} deriving Show

worldPos :: Lens' (Vertex a) (World a)
worldPos = lens _worldPos $ \c v -> c {_worldPos = v}
axisPos :: Lens' (Vertex a) (Ratio a)
axisPos = lens _axisPos $ \c v -> c {_axisPos = v}
anglePos :: Lens' (Vertex a) (Rotate a)
anglePos = lens _anglePos $ \c v -> c {_anglePos = v}
direction :: Lens' (Vertex a) (World a)
direction = lens _direction $ \c v -> c {_direction = v}

instance ToAny (Vertex R) where
  toAny (Vertex w (Ratio r a) (Rotate t) d) = toObject $ fmap toAny <$> [
      ("wx", w^.x),
      ("wy", w^.y),
      ("wz", w^.z),
      ("lx", r*a*cos t),
      ("ly", r*a*sin t),
      ("r", r),
      ("a", a),
      ("t", t),
      ("dx", d^.x),
      ("dy", d^.y),
      ("dz", d^.z)
    ]

-- Polygon

data Polygon a = Polygon !(Vertex a) !(Vertex a) !(Vertex a)
  deriving Show

instance V1 (Polygon a) (Vertex a) where
  x = lens (\(Polygon x _ _) -> x) $ \(Polygon _ y z) x -> Polygon x y z
instance V2 (Polygon a) (Vertex a) where
  y = lens (\(Polygon _ y _) -> y) $ \(Polygon x _ z) y -> Polygon x y z
instance V3 (Polygon a) (Vertex a) where
  z = lens (\(Polygon _ _ z) -> z) $ \(Polygon x y _) z -> Polygon x y z

instance ToAny (Polygon R) where
  toAny (Polygon x y z) = listToAny [x,y,z]

-- Gravity

newtype Gravity a = Gravity {unGravity :: World R -> World R}

instance Show (Gravity a) where
  show _ = "[Gravity]"

-- Object

data Object = Object {
  -- property
  _shape :: !Shape,
  _gravity :: !(Gravity R),
  _massInv :: !(Pos R),
  -- state
  _coord :: !(Pos R),
  _veloc :: !(Pos R),
  _rotAxis :: !(World R),
  -- cache
  _surface :: !(World R),
  _polygon :: !JSAny, -- [Polygon R],
  _outline :: !JSAny, -- [Vertex R],
  _enclose :: !R
} deriving Show

shape :: Lens' Object Shape
shape = lens _shape $ \c v -> c {_shape = v}
gravity :: Lens' Object (World R -> World R)
gravity = lens (unGravity._gravity) $ \c v -> c {_gravity = Gravity v}
massInv :: Lens' Object (Pos R)
massInv = lens _massInv $ \c v -> c {_massInv = v}

coord :: Lens' Object (Pos R)
coord = lens _coord $ \c v -> c {_coord = v}
veloc :: Lens' Object (Pos R)
veloc = lens _veloc $ \c v -> c {_veloc = v}
rotAxis :: Lens' Object (World R)
rotAxis = lens _rotAxis $ \c v -> c {_rotAxis = v}

surface :: Lens' Object (World R)
surface = lens _surface $ \c v -> c {_surface = v}
polygon :: Lens' Object JSAny
polygon = lens _polygon $ \c v -> c {_polygon = v}
outline :: Lens' Object JSAny
outline = lens _outline $ \c v -> c {_outline = v}
enclose :: Lens' Object R
enclose = lens _enclose $ \c v -> c {_enclose = v}

static :: SimpleGetter Object Object
static = to $ (gravity .~ const 0) . (massInv .~ 0)

type ObjIx = Int
type PhysWorld = A.Array ObjIx Object

circle :: R -> Shape
circle r = Shape $ \_ -> r

square :: R -> Shape
square r = Shape $ \a -> r / cos (fmod a (pi/2) - pi/4)

type Density = R

make :: Shape -> Density -> Pos R -> Pos R -> World R -> Object
make (Shape s) rho c v ra = let
    aN = fromIntegral angleCount
    r i = s (2*pi*i/aN)
    integrate :: Int -> R
    integrate e = 2*pi/aN * sum [ ds (r i) (r (i+1)) | i <- [0..aN-1] ] where
      ds r1 r2 = rr (2+e) / fa where
        fa = (2 + fromIntegral e) * (1 + fromIntegral e)
        rr x = if r1 == r2 then fromIntegral x * r1^(x-1) else (r1^x - r2^x) / (r1 - r2)
    mass = integrate 1 * rho  -- 1 * J = r^1
    inertia = integrate 3 * rho -- r^2 * J = r^3
    mi = Pos (scale (1/mass)) (Rotate (1/inertia))
    g = Gravity $ \p -> World 0 (-4) 0
  in fitO $ Object (Shape s) g mi c v ra 0 nullValue nullValue 0

generatePolygon :: Object -> ([Polygon R], [Vertex R], R)
generatePolygon o = S.evalState ?? o $ do
  Pos c (Rotate r) <- use coord
  Shape sf <- use shape
  ra <- use rotAxis
  n <- use surface
  let
    ax = o^.rotAxis
    ay = cross ax (o^.surface)
    aC = fromIntegral angleCount
    pC = fromIntegral proceedCount
    vss = map ?? [0..aC-1] $ \ai -> let
        a = ai/aC*2*pi
        s = sf a
        a' = a + r
        dir = ax * scale (cos a') + ay * scale (sin a')
        c' = Vertex c (Ratio 0 s) (Rotate a) 0
      in (c',) $ S.evalState ?? (c,dir) $ do
        for [1..pC] $ \i -> do
          v <- use _2
          _1 += v * scale (s/pC)
          (p,n) <- use $ _1.to fitP
          _1 .= p
          _2 %= fitR n
          v' <- use _2
          return $ Vertex p (Ratio (i/pC) s) (Rotate a) v'
  let
    comp :: (Vertex R, [Vertex R]) -> (Vertex R, [Vertex R]) -> [Polygon R]
    comp (cv,xs) (_,ys) = let
        make :: (Vertex R, Vertex R) -> (Vertex R, Vertex R) -> [Polygon R]
        make (a,b) (c,d) = [Polygon a b c, Polygon b c d]
        rects = zipWith make (zip xs $ tail xs) (zip ys $ tail ys)
      in Polygon cv (head xs) (head ys) : concat rects
    ps = concat $ zipWith comp vss (tail $ vss ++ [head vss])
    ls = map (\(_,vs) -> last vs) vss
    enc = maximum $ map (sf . (*(2*pi/aC))) $ [0..aC-1]
  return (ps, ls, enc)

fitO :: Object -> Object
fitO o = let
    (p,n) = fitP $ o^.coord.place
    v = fitV n $ o^.veloc.place
    ra = fitR n $ o^.rotAxis
  in o
    & coord.place .~ p
    & veloc.place .~ v
    & rotAxis .~ ra
    & surface .~ n
    & \o -> let
        (p,l,e) = generatePolygon o
      in o
        & polygon .~ toAny p
        & outline .~ toAny l
        & enclose .~ e

passObject :: Int -> Object -> IO ()
passObject = ffi "__strict(passObject)"

instance ToAny Object where
  toAny o = toObject [
      ("x", toAny $ o^.coord.place.x),
      ("y", toAny $ o^.coord.place.y),
      ("z", toAny $ o^.coord.place.z),
      ("polygon", o^.polygon),
      ("outline", o^.outline),
      ("enclose", toAny $ o^.enclose)
    ]

drawObjects :: IO ()
drawObjects = ffi "__strict(drawObjects)"
