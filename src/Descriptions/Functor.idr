module Descriptions.Functor

import Descriptions.Core

%default total
%access export
%auto_implicits off

mutual
  gmapd : {a, b, Ix: _} -> (dr: PDesc (S Z) Ix) -> PConstraints1 Functor dr ->
                           (d: PDesc (S Z) Ix) -> PConstraints1 Functor d ->
                           (a -> b) -> {ix: Ix} -> (PSynthesize d a (PData dr a) ix) -> (PSynthesize d b (PData dr b) ix)
  gmapd dr constraintsr (PRet ix) constraints f Refl = Refl
  gmapd dr constraintsr (PArg A kdesc) constraints f (arg ** rest) = (arg ** gmapd dr constraintsr (kdesc arg) (constraints arg) f rest)
  gmapd dr constraintsr (PPar FZ kdesc) constraints f (par ** rest) = (f par ** gmapd dr constraintsr kdesc constraints f rest)
  gmapd _ _ (PPar (FS FZ) _) _ _ _ impossible
  gmapd _ _ (PPar (FS (FS _)) _) _ _ _ impossible
  gmapd dr constraintsr (PMap t FZ kdesc) (tfunc, constraints) f (targ ** rest) = (map @{tfunc} f targ ** gmapd dr constraintsr kdesc constraints f rest)
  gmapd _ _ (PMap _ (FS FZ) _) _ _ _ impossible
  gmapd _ _ (PMap _ (FS (FS _)) _) _ _ _ impossible
  gmapd dr constraintsr (PRec ix kdesc) constraints f (rec ** rest) = (gmap dr constraintsr f rec ** gmapd dr constraintsr kdesc constraints f rest)

  gmap : {a, b, Ix: _} -> (d: PDesc (S Z) Ix) -> PConstraints1 Functor d -> {ix: Ix} -> (a -> b) -> (PData d a ix) -> (PData d b ix)
  gmap d constraints f (Con x) = Con (assert_total $ gmapd d constraints d constraints f x)
