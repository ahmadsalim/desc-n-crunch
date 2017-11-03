module Descriptions.Foldable

import Descriptions.Core

%default total
%access export
%auto_implicits off

using (m: Type)
  mutual
    gconcatMapd : Monoid m => {a, Ix: _} -> (dR: PDesc (S Z) Ix) -> PConstraints1 Foldable dR
                                         -> (d: PDesc (S Z) Ix) -> PConstraints1 Foldable d
                                         -> (a -> m) -> {ix: Ix} -> PSynthesize d a (PData dR a) ix -> m
    gconcatMapd _  _            (PRet _)       _           _ Refl          = neutral
    gconcatMapd dR cstrsR (PArg _ kdesc)   cstrs f (arg ** rest) =
      gconcatMapd dR cstrsR (kdesc arg) (cstrs arg) f rest
    gconcatMapd dR cstrsR (PPar  FZ kdesc) cstrs f (par ** rest) =
      f par <+> gconcatMapd dR cstrsR kdesc cstrs f rest
    gconcatMapd _  _            (PPar (FS  FZ) _)     _ _ _ impossible
    gconcatMapd _  _            (PPar (FS (FS _)) _) _ _ _ impossible
    gconcatMapd dR cstrsR (PMap _  FZ kdesc) (foldable, cstrs) f (targ ** rest) =
      concatMap @{foldable} f targ <+> gconcatMapd dR cstrsR kdesc cstrs f rest
    gconcatMapd _  _            (PMap _ (FS  FZ) _)    _ _ _ impossible
    gconcatMapd _  _            (PMap _ (FS (FS _)) _) _ _ _ impossible
    gconcatMapd dR cstrsR (PRec _ kdesc) cstrs f (rec ** rest) =
      gconcatMap dR cstrsR f rec <+> gconcatMapd dR cstrsR kdesc cstrs f rest

    gconcatMap : Monoid m => {a, Ix: _} -> (d: PDesc (S Z) Ix) -> PConstraints1 Foldable d -> (a -> m) -> {ix: Ix} -> PData d a ix -> m
    gconcatMap d cstrs f (Con x) = assert_total $ gconcatMapd d cstrs d cstrs f x
