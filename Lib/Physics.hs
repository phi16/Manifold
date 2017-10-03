{-# LANGUAGE PackageImports #-}
{-# LANGUAGE MultiWayIf #-}

module Lib.Physics (
  module Lib.Physics.Types,
  nextFrame,
  collide,
  generateConstraints,
  solveConstraints
) where

import Lib.Util
import Lib.Physics.Types
import qualified "mtl" Control.Monad.State as S
import qualified Data.Array as A
import Data.Traversable
import Data.Maybe

dt :: R
dt = 0.2

nextFrame :: S.StateT World IO ()
nextFrame = do
  traverse %= \o -> o & veloc +~ o^.gravity * scale (dt * sin (o^.coord.y / scrH * 2 * pi))
  cs <- generateConstraints
  solveConstraints cs
  traverse %= \o -> o & coord +~ o^.veloc * scale dt
  traverse %= normalizeObject
  return ()

collide' :: Object -> Object -> [ContactPoint]
collide' d1 d2 = let
      c1 = Local (d1^.coord.x) (d1^.coord.y)
      c2 = Local (d2^.coord.x) (d2^.coord.y)
      d = c1 - c2
  in case (d1^.shape, d2^.shape) of
    (Circle r1, Circle r2) -> let
        nd = norm d
        rr = r1 + r2
      in if nd > rr
        then []
        else let
            n = normalize d
            l1 = - n * scale r1
            l2 = n * scale r2
            depth = rr - nd
          in [ContactPoint l1 l2 n n depth]
    (Circle r1, Rect w2 h2) -> let
        o = rotate (-d2^.coord.t) d
        np = o - Local (clamp (-w2/2,w2/2) $ o^.x) (clamp (-h2/2,h2/2) $ o^.y)
        nd = norm np
        rr = r1
      in if nd > rr
        then []
        else let
            ax = w2/2 - abs (o^.x)
            ay = h2/2 - abs (o^.y)
            (n',depth) = if
              | ax <= 0 || ay <= 0 -> (normalize np, rr - nd)
              | ax <= ay -> (Local (signum $ np^.x) 0, rr + ax)
              | ax >= ay -> (Local 0 (signum $ np^.y), rr + ay)
            n = rotate (d2^.coord.t) n'
            p1 = c1 - n * scale r1
            p2 = p1 + n * scale depth
            l1 = p1 - c1
            l2 = p2 - c2
          in [ContactPoint l1 l2 n n depth]
    (Rect w1 h1, Circle r2) -> let
        cs = collide' d2 d1
        f (ContactPoint l2 l1 n2 n1 depth) = ContactPoint l1 l2 (-n1) (-n2) depth
      in map f cs
    (Rect w1 h1, Rect w2 h2) -> let
        vs = [Local (-1) (-1), Local (-1) 1, Local 1 1, Local 1 (-1), Local (-1) (-1)]
        difs xs = zip xs (tail xs)
        tr1 v = Local (d1^.coord.x) (d1^.coord.y) + rotate (d1^.coord.t) (v * Local w1 h1 * scale 0.5)
        tr2 v = Local (d2^.coord.x) (d2^.coord.y) + rotate (d2^.coord.t) (v * Local w2 h2 * scale 0.5)
        v1 = map tr1 vs
        v2 = map tr2 vs
        f1 = difs v1
        f2 = difs v2
        in1 = map (\e -> map (inner e) $ tail v2) f1
        in2 = map (\e -> map (inner e) $ tail v1) f2
        inner :: (Local,Local) -> Local -> Maybe R
        inner (s1,s2) x = let
            n = perp (s2-s1)
            l = (dot (n*x) - dot (n*s1)) / norm n
          in if l >= 0 then Nothing else Just l
      in if any (all (==Nothing)) $ in1 ++ in2
        then []
        else let
            mf1 = snd $ maximum $ zip (map (minimum . filter isJust) in1) [0..3]
            mf2 = snd $ maximum $ zip (map (minimum . filter isJust) in2) [0..3]
            mp1 = minimum $ filter isJust $ in1 !! mf1
            mp2 = minimum $ filter isJust $ in2 !! mf2
            w = mp1 > mp2
            (Just d',f') = if w then (mp1,mf1) else (mp2,mf2)
            (fA,fB) = if w then (f1,f2) else (f2,f1)
            fr@(fr1,fr2) = fA !! f'
            vn = tail $ if w then v2 else v1
            x' = snd $ minimum $ filter (isJust.fst) $ zip (map (inner fr) vn) [0..3]
            xa@(xa1,xa2) = (\(a,b) -> (b,a)) $ fB !! x'
            xb@(xb1,xb2) = fB !! ((x'+1)`mod`4)
            frn = normalize $ fr2-fr1
            xan = normalize $ xa2-xa1
            xbn = normalize $ xb2-xb1
            xd@(xd1,xd2) = if abs (dot $ frn*xan) > abs (dot $ frn*xbn) then xa else xb
            poi :: Local -> R
            poi x = let
                p0 = dot(fr1*frn)
                px = dot(x*frn)
                p1 = dot(fr2*frn)
              in (px-p0) / (p1-p0)
            clamp :: R -> R
            clamp x = min 1 $ max 0 x
            pd@(pd1,pd2) = xd & both %~ poi
            iop :: R -> Local
            iop x = mix xd1 xd2 (pd2-x) (x-pd1)
            (ce1,ce2) = pd & both %~ iop.clamp
            cn1 = case inner fr ce1 of {Just d -> [(ce1,-d)]; _ -> []}
            cn2 = case inner fr ce2 of {Just d -> [(ce2,-d)]; _ -> []}
            n' = perp frn
            pA' = cn1 ++ cn2
            pA = map fst pA'
            pB = map (\(p,d) -> p + n' * scale d) pA'
            depth = map snd pA'
            p1 = if w then pB else pA
            p2 = if w then pA else pB
            n = if w then -n' else n'
            l1 = map (subtract c1) p1
            l2 = map (subtract c2) p2
          in zipWith3 (\l1 l2 depth -> ContactPoint l1 l2 n n depth) l1 l2 depth

collide :: Object -> Object -> [ContactPoint]
collide d1 d2 = do
  i <- [-1..1]
  j <- [-1..1]
  let
    coord' = moveCoord (i,j) $ d2^.coord
    veloc' = flipVeloc (i,j) $ d2^.veloc
    gravity' = flipVeloc (i,j) $ d2^.gravity
    d2' = Object (d2^.shape) coord' veloc' gravity' (d2^.massInv)
    sameObject = d1^.coord.x == d2^.coord.x && d1^.coord.y == d2^.coord.y && d1^.coord.t == d2^.coord.t
  if sameObject && i==0 && j==0 then [] else [()]
  c <- collide' d1 d2'
  return $ c & local2 %~ flipLocal (i,j) & normal2 %~ flipLocal (i,j)

generateConstraints :: S.StateT World IO [Constraint]
generateConstraints = do
  a <- use id
  let (s,f) = A.bounds a
  fmap concat $ for [s..f] $ \i1 -> do
    fmap concat $ for [i1+1..f] $ \i2 -> do
      let
        d1 = a ^?! ix i1
        d2 = a ^?! ix i2
        cs = collide d1 d2
        f (ContactPoint l1 l2 n1 n2 d) = Constraint i1 i2 j1 j2 d where
          j1 = Coord (n1^.x) (n1^.y) (cross l1 n1)
          j2 = Coord (n2^.x) (n2^.y) (cross l2 n2)
      return $ map f cs

solveConstraints :: [Constraint] -> S.StateT World IO ()
solveConstraints cs = replicateM_ 5 $ for cs $ \c -> do
  d1' <- preuse $ ix (c^.o1)
  d2' <- preuse $ ix (c^.o2)
  let
    d1 = fromJust d1'
    d2 = fromJust d2'
    bias = 0.1 * c^.depth / dt
    jvt = jv c (d1^.veloc) (d2^.veloc)
    jmjt = dot (c^.j1 * d1^.massInv * c^.j1) + dot (c^.j2 * d2^.massInv * c^.j2)
    ldt = - (jvt - bias) / jmjt
  when (jmjt /= 0 && ldt >= 0) $ do
    let sameScale = if c^.o1 == c^.o2 then 0.6 else 1
    ix (c^.o1).veloc += d1^.massInv * c^.j1 * scale (ldt * sameScale)
    ix (c^.o2).veloc -= d2^.massInv * c^.j2 * scale (ldt * sameScale)
