module Descriptions.Functor

import Descriptions.Core
import Interfaces

%default total
%access export
%auto_implicits off

mutual
  gmapd : {a, b, e, Ix: _} -> (dr: PTaggedDesc e (S Z) Ix) -> PTaggedConstraints1 VFunctor dr ->
                              (d: PDesc (S Z) Ix) -> PConstraints1 VFunctor d ->
                              (a -> b) -> {ix: Ix} -> (PSynthesize d a (PTaggedData dr a) ix) -> (PSynthesize d b (PTaggedData dr b) ix)
  gmapd dr constraintsr (PRet ix) constraints f Refl = Refl
  gmapd dr constraintsr (PArg A kdesc) constraints f (arg ** rest) = (arg ** gmapd dr constraintsr (kdesc arg) (constraints arg) f rest)
  gmapd dr constraintsr (PPar FZ kdesc) constraints f (par ** rest) = (f par ** gmapd dr constraintsr kdesc constraints f rest)
  gmapd _ _ (PPar (FS FZ) _) _ _ _ impossible
  gmapd _ _ (PPar (FS (FS _)) _) _ _ _ impossible
  gmapd dr constraintsr (PMap t FZ kdesc) (tfunc, constraints) f (targ ** rest) = (map f targ ** gmapd dr constraintsr kdesc constraints f rest)
  gmapd _ _ (PMap _ (FS FZ) _) _ _ _ impossible
  gmapd _ _ (PMap _ (FS (FS _)) _) _ _ _ impossible
  gmapd dr constraintsr (PRec ix kdesc) constraints f (rec ** rest) = (gmap dr constraintsr f rec ** gmapd dr constraintsr kdesc constraints f rest)

  gmap : {a, b, e, Ix: _} -> (d: PTaggedDesc e (S Z) Ix) -> PTaggedConstraints1 VFunctor d -> {ix: Ix} -> (a -> b) -> (PTaggedData d a ix) -> (PTaggedData d b ix)
  gmap d constraints f (Con (l ** t ** r)) = Con (l ** t ** assert_total $ gmapd d constraints (d l t) (constraints l t) f r)
