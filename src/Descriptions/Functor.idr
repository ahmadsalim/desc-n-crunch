module Descriptions.Functor

import Descriptions.Core
import Interfaces

%default total
%access export
%auto_implicits off

mutual
  gmapd : {a, b, Ix: _} -> (dR: PDesc (S Z) Ix) -> PConstraints1 VFunctor dR
                        -> (d: PDesc (S Z) Ix) -> PConstraints1 VFunctor d
                        -> (a -> b) -> {ix: Ix} -> PSynthesize d a (PData dR a) ix
                        -> PSynthesize d b (PData dR b) ix
  gmapd _  _            (PRet _) _ _ Refl = Refl
  gmapd dR cstrsR (PArg _ kdesc) cstrs f (arg ** rest) =
    (arg ** gmapd dR cstrsR (kdesc arg) (cstrs arg) f rest)
  gmapd dR cstrsR (PPar FZ kdesc) cstrs f (par ** rest) =
    (f par ** gmapd dR cstrsR kdesc cstrs f rest)
  gmapd _  _            (PPar (FS FZ) _) _ _ _ impossible
  gmapd _  _            (PPar (FS (FS _)) _) _ _ _ impossible
  gmapd dR cstrsR (PMap _ FZ kdesc) (_, cstrs) f (targ ** rest) =
    (map f targ ** gmapd dR cstrsR kdesc cstrs f rest)
  gmapd _  _            (PMap _ (FS FZ) _) _ _ _ impossible
  gmapd _  _            (PMap _ (FS (FS _)) _) _ _ _ impossible
  gmapd dR cstrsR (PRec _ kdesc) cstrs f (rec ** rest) =
    (gmap dR cstrsR f rec ** gmapd dR cstrsR kdesc cstrs f rest)

  gmap : {a, b, Ix: _} -> (d: PDesc (S Z) Ix) -> PConstraints1 VFunctor d
                       -> {ix: Ix} -> (a -> b) -> PData d a ix -> PData d b ix
  gmap d cstrs f (Con x) = Con (assert_total $ gmapd d cstrs d cstrs f x)

mutual
  gmapdIdH : {a, Ix: _} -> (dR: PDesc 1 Ix) -> (cstrsR: PConstraints1 VFunctor dR)
                        -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VFunctor d)
                        -> {ix: Ix} -> (X: PSynthesize d a (PData dR a) ix)
                        -> gmapd dR cstrsR d cstrs id X = id X
  gmapdIdH     _  _            (PRet _) _ Refl = Refl
  gmapdIdH     dR cstrsR (PArg _ kdesc) cstrs (arg ** rest) =
    cong $ gmapdIdH dR cstrsR (kdesc arg) (cstrs arg) rest
  gmapdIdH     dR cstrsR (PPar FZ kdesc) cstrs (_ ** rest) =
    dpairEq Refl (gmapdIdH dR cstrsR kdesc cstrs rest)
  gmapdIdH     _  _            (PPar (FS FZ) _) _ _ impossible
  gmapdIdH     _  _            (PPar (FS (FS _)) _) _ _ impossible
  gmapdIdH {a} dR cstrsR (PMap f  FZ kdesc) (vfunta, vfunr) (ta ** rest) =
    dpairEq (fundet {a = f a} (mapId @{vfunta} {a}) ta) (gmapdIdH dR cstrsR kdesc vfunr rest)
  gmapdIdH     _  _            (PMap _ (FS FZ) _) _ _ impossible
  gmapdIdH     _  _            (PMap _ (FS (FS _)) _) _ _ impossible
  gmapdIdH     dR cstrsR (PRec _ kdesc) cstrs (rec ** rest) =
    dpairEq (gmapIdH dR cstrsR rec) (gmapdIdH dR cstrsR kdesc cstrs rest)

  gmapIdH : {a, Ix: _} -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VFunctor d)
                       -> {ix: Ix} -> (X: PData d a ix) -> gmap d cstrs id X = id X
  gmapIdH d cstrs (Con x) = assert_total $ cong $ gmapdIdH d cstrs d cstrs x

gmapId : {a, Ix: _} -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VFunctor d) -> {ix: Ix} -> gmap d cstrs id = id
gmapId d cstrs = funext (gmapIdH d cstrs)

mutual
  gmapdComposeH : {a, b, c, Ix: _} -> (dR: PDesc 1 Ix) -> (cstrsR: PConstraints1 VFunctor dR)
                                   -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VFunctor d)
                                   -> {ix: Ix} -> (f : b -> c) -> (g : a -> b) -> (X : PSynthesize d a (PData dR a) ix)
                                   -> gmapd dR cstrsR d cstrs (f . g) X = (gmapd dR cstrsR d cstrs f . gmapd dR cstrsR d cstrs g) X
  gmapdComposeH _  _            (PRet _)       _           _ _ Refl = Refl
  gmapdComposeH dR cstrsR (PArg _ kdesc) cstrs f g (arg ** rest) =
    dpairEq Refl (gmapdComposeH dR cstrsR (kdesc arg) (cstrs arg) f g rest)
  gmapdComposeH dR cstrsR (PPar  FZ kdesc) cstrs f g (a ** rest) =
    dpairEq Refl (gmapdComposeH dR cstrsR kdesc cstrs f g rest)
  gmapdComposeH _  _            (PPar (FS  FZ) _)    _ _ _ _ impossible
  gmapdComposeH _  _            (PPar (FS (FS _)) _) _ _ _ _ impossible
  gmapdComposeH {a} {b} {c} dR cstrsR (PMap _ FZ kdesc) (vfunta, vfunr) f g (ta ** rest) =
    dpairEq (fundet (mapCompose @{vfunta} {a} {b} {c} {g = f} {h = g}) ta) (gmapdComposeH dR cstrsR kdesc vfunr f g rest)
  gmapdComposeH _ _ (PMap _ (FS FZ) _) _ _ _ _ impossible
  gmapdComposeH _ _ (PMap _ (FS (FS _)) _) _ _ _ _ impossible
  gmapdComposeH dR cstrsR (PRec ix kdesc) cstrs f g (rec ** rest) =
    dpairEq (gmapComposeH dR cstrsR f g rec) (gmapdComposeH dR cstrsR kdesc cstrs f g rest)

  gmapComposeH : {a, b, c, Ix: _} -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VFunctor d)
                                  -> {ix: Ix} -> (f : b -> c) -> (g : a -> b) -> (X : PData d a ix)
                                  -> gmap d cstrs (f . g) X = (gmap d cstrs f . gmap d cstrs g) X
  gmapComposeH d cstrs f g (Con x) = assert_total $ cong $ gmapdComposeH d cstrs d cstrs f g x

gmapCompose : {a, b, c, Ix: _} -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VFunctor d)
                               -> {ix: Ix} -> (f : b -> c) -> (g : a -> b)
                               -> gmap d cstrs (f . g) = gmap d cstrs f . gmap d cstrs g
gmapCompose d cstrs f g = funext (gmapComposeH d cstrs f g)
