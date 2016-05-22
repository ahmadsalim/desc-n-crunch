module Interfaces

import public Data.So

interface Eq a => VEq a where
  eqReflexive  : {x : a} -> So (x == x)
  eqSymmetric  : {x,y : a} -> So (y == x) -> So (x == y)
  eqTransitive : {x,y,z : a} -> So (x == z) -> So (z == y) -> So (x == y)

interface VEq a => SEq a where
  eqReflective : {x,y : a} -> So (x == y) -> x = y

interface Ord a => VOrd a where
  leqReflexive : {x : a} -> So (x <= x)
  leqTransitive : {x,y,z : a} -> So (x <= z) -> So (z <= y) -> So (x <= y)
  leqAntisymmetric : {x,y : a} -> So (x <= y) -> So (y <= x) -> So (x == y)
  leqTotal : {x, y: a} -> Either (So (x <= y)) (So (y <= x))

interface (VOrd a, SEq a) => SOrd a where

interface Functor f => VFunctor (f : Type -> Type) where
  mapWithId      : {a : Type} -> {x : f a} -> map (id {a = a}) x = id {a = f a} x
  mapWithCompose : {a,b,c : Type} -> {x : f a} -> {g : b -> c} -> {h : a -> b} -> map (g . h) x = (map g . map h) x
