{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}

module Lib.Constraint where

import Lib.Util
import Lib.Object
import Lib.World

-- ContactPoint

data ContactPoint = ContactPoint {
  _contact1 :: Vertex R,
  _contact2 :: Vertex R,
  _normal1 :: World R,
  _normal2 :: World R
} deriving Show

contact1 :: Lens' ContactPoint (Vertex R)
contact1 = lens _contact1 $ \c v -> c {_contact1 = v}
contact2 :: Lens' ContactPoint (Vertex R)
contact2 = lens _contact2 $ \c v -> c {_contact2 = v}
normal1 :: Lens' ContactPoint (World R)
normal1 = lens _normal1 $ \c v -> c {_normal1 = v}
normal2 :: Lens' ContactPoint (World R)
normal2 = lens _normal2 $ \c v -> c {_normal2 = v}

-- Constraint

type Constraint = () -- TODO
