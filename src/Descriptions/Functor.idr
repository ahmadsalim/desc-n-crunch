module Descriptions.Functor

import Descriptions.Core
import Interfaces

%default total
%access export
%auto_implicits off

mutual
  gmapd : {a, b, Ix: _} -> (dr: PDesc (S Z) Ix) -> PConstraints1 VFunctor dr ->
                              (d: PDesc (S Z) Ix) -> PConstraints1 VFunctor d ->
                              (a -> b) -> {ix: Ix} -> (PSynthesize d a (PData dr a) ix) -> (PSynthesize d b (PData dr b) ix)
  gmapd _  _            (PRet _) _ _ Refl = Refl
  gmapd dr constraintsr (PArg _ kdesc) constraints f (arg ** rest) =
    (arg ** gmapd dr constraintsr (kdesc arg) (constraints arg) f rest)
  gmapd dr constraintsr (PPar  FZ kdesc) constraints f (par ** rest) =
    (f par ** gmapd dr constraintsr kdesc constraints f rest)
  gmapd _  _            (PPar (FS FZ) _) _ _ _ impossible
  gmapd _  _            (PPar (FS (FS _)) _) _ _ _ impossible
  gmapd dr constraintsr (PMap _ FZ kdesc) (_, constraints) f (targ ** rest) =
    (map f targ ** gmapd dr constraintsr kdesc constraints f rest)
  gmapd _  _            (PMap _ (FS FZ) _) _ _ _ impossible
  gmapd _  _            (PMap _ (FS (FS _)) _) _ _ _ impossible
  gmapd dr constraintsr (PRec _ kdesc) constraints f (rec ** rest) =
    (gmap dr constraintsr f rec ** gmapd dr constraintsr kdesc constraints f rest)

  gmap : {a, b, Ix: _} -> (d: PDesc (S Z) Ix) -> PConstraints1 VFunctor d -> {ix: Ix} -> (a -> b) -> (PData d a ix) -> (PData d b ix)
  gmap d constraints f (Con x) = Con (assert_total $ gmapd d constraints d constraints f x)

mutual
  gmapdIdH : {a, Ix: _} -> (dr: PDesc 1 Ix) -> (constraintsr: PConstraints1 VFunctor dr) -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VFunctor d) -> {ix: Ix} -> (X: PSynthesize d a (PData dr a) ix) -> (gmapd dr constraintsr d constraints id X = id X)
  gmapdIdH     _  _            (PRet _) _ Refl = Refl
  gmapdIdH     dr constraintsr (PArg _ kdesc) constraints (arg ** rest) =
    cong $ gmapdIdH dr constraintsr (kdesc arg) (constraints arg) rest
  gmapdIdH     dr constraintsr (PPar FZ kdesc) constraints (_ ** rest) with (gmapdIdH dr constraintsr kdesc constraints rest)
    | prf = dpairEq Refl prf
  gmapdIdH     _  _            (PPar (FS FZ) _) _ _ impossible
  gmapdIdH     _  _            (PPar (FS (FS _)) _) _ _ impossible
  gmapdIdH {a} dr constraintsr (PMap f  FZ kdesc) (vfunta, vfunr) (ta ** rest) with (mapId @{vfunta} {a})
    gmapdIdH {a} dr constraintsr (PMap f FZ kdesc) (_, vfunr) (ta ** rest) | prf with (gmapdIdH dr constraintsr kdesc vfunr rest)
      gmapdIdH {a} dr constraintsr (PMap f FZ kdesc) (_, vfunr) (ta ** rest) | prf | prf' = dpairEq (fundet {a = f a} prf ta) prf'
  gmapdIdH     _  _            (PMap _ (FS FZ) _) _ _ impossible
  gmapdIdH     _  _            (PMap _ (FS (FS _)) _) _ _ impossible
  gmapdIdH     dr constraintsr (PRec _ kdesc) constraints (rec ** rest) with (gmapIdH dr constraintsr rec)
    gmapdIdH dr constraintsr (PRec _ kdesc) constraints (rec ** rest) | prf with (gmapdIdH dr constraintsr kdesc constraints rest)
      gmapdIdH _ _ _ _ _ | prf | prf' = dpairEq prf prf'

  gmapIdH : {a, Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VFunctor d) -> {ix: Ix} -> (X: PData d a ix) -> (gmap d constraints id X = id X)
  gmapIdH d constraints (Con x) = assert_total $ cong $ gmapdIdH d constraints d constraints x

gmapId : {a, Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VFunctor d) -> {ix: Ix} -> (gmap d constraints id = id)
gmapId d constraints = funext (gmapIdH d constraints)

mutual
  gmapdComposeH : {a, b, c, Ix: _} -> (dr: PDesc 1 Ix) -> (constraintsr: PConstraints1 VFunctor dr) -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VFunctor d) -> {ix: Ix} -> (f : b -> c) -> (g : a -> b) -> (X : PSynthesize d a (PData dr a) ix) -> (gmapd dr constraintsr d constraints (f . g) X = (gmapd dr constraintsr d constraints f . gmapd dr constraintsr d constraints g) X)
  gmapdComposeH _  _            (PRet _)       _           _ _ Refl = Refl
  gmapdComposeH dr constraintsr (PArg _ kdesc) constraints f g (arg ** rest) with (gmapdComposeH dr constraintsr (kdesc arg) (constraints arg) f g rest)
    | prf = dpairEq Refl prf
  gmapdComposeH dr constraintsr (PPar  FZ kdesc) constraints f g (a ** rest) with (gmapdComposeH dr constraintsr kdesc constraints f g rest)
    | prf = dpairEq Refl prf
  gmapdComposeH _  _            (PPar (FS  FZ) _)    _ _ _ _ impossible
  gmapdComposeH _  _            (PPar (FS (FS _)) _) _ _ _ _ impossible
  gmapdComposeH {a} {b} {c} dr constraintsr (PMap x FZ kdesc) (vfunta, vfunr) f g (ta ** rest) with (mapCompose @{vfunta} {a} {b} {c} {g = f} {h = g})
    gmapdComposeH dr constraintsr (PMap _ FZ kdesc) (_, vfunr) f g (ta ** rest) | prf with (gmapdComposeH dr constraintsr kdesc vfunr f g rest)
      gmapdComposeH _ _ _ _ _ _ (ta ** _) | prf | prf' = dpairEq (fundet prf ta) prf'
  gmapdComposeH _ _ (PMap _ (FS FZ) _) _ _ _ _ impossible
  gmapdComposeH _ _ (PMap _ (FS (FS _)) _) _ _ _ _ impossible
  gmapdComposeH dr constraintsr (PRec ix kdesc) constraints f g (rec ** rest) with (gmapComposeH dr constraintsr f g rec)
    gmapdComposeH dr constraintsr (PRec _ kdesc) constraints f g (_ ** rest) | prf with (gmapdComposeH dr constraintsr kdesc constraints f g rest)
      gmapdComposeH _ _ _ _ _ _ _ | prf | prf' = dpairEq prf prf'

  gmapComposeH : {a, b, c, Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VFunctor d) -> {ix: Ix} -> (f : b -> c) -> (g : a -> b) -> (X : PData d a ix) -> (gmap d constraints (f . g) X = (gmap d constraints f . gmap d constraints g) X)
  gmapComposeH d constraints f g (Con x) = assert_total $ cong $ gmapdComposeH d constraints d constraints f g x

gmapCompose : {a, b, c, Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VFunctor d) -> {ix: Ix} -> (f : b -> c) -> (g : a -> b) -> (gmap d constraints (f . g) = gmap d constraints f . gmap d constraints g)
gmapCompose d constraints f g = funext (gmapComposeH d constraints f g)
