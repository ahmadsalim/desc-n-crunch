module Descriptions.Foldable

import Descriptions.Core

%default total
%access export
%auto_implicits off

using (m: Type)
  mutual
    gconcatMapd : Monoid m => {a, Ix: _} -> (dr: PDesc (S Z) Ix) -> PConstraints1 Foldable dr
                                         -> (d: PDesc (S Z) Ix) -> PConstraints1 Foldable d
                                         -> (a -> m) -> {ix: Ix} -> PSynthesize d a (PData dr a) ix -> m
    gconcatMapd _  _            (PRet _)       _           _ Refl          = neutral
    gconcatMapd dr constraintsr (PArg _ kdesc)   constraints f (arg ** rest) =
      gconcatMapd dr constraintsr (kdesc arg) (constraints arg) f rest
    gconcatMapd dr constraintsr (PPar  FZ kdesc) constraints f (par ** rest) =
      f par <+> gconcatMapd dr constraintsr kdesc constraints f rest
    gconcatMapd _  _            (PPar (FS  FZ) _)     _ _ _ impossible
    gconcatMapd _  _            (PPar (FS (FS _)) _) _ _ _ impossible
    gconcatMapd dr constraintsr (PMap _  FZ kdesc) (foldable, constraints) f (targ ** rest) =
      concatMap @{foldable} f targ <+> gconcatMapd dr constraintsr kdesc constraints f rest
    gconcatMapd _  _            (PMap _ (FS  FZ) _)    _ _ _ impossible
    gconcatMapd _  _            (PMap _ (FS (FS _)) _) _ _ _ impossible
    gconcatMapd dr constraintsr (PRec _ kdesc) constraints f (rec ** rest) =
      gconcatMap dr constraintsr f rec <+> gconcatMapd dr constraintsr kdesc constraints f rest

    gconcatMap : Monoid m => {a, Ix: _} -> (d: PDesc (S Z) Ix) -> PConstraints1 Foldable d -> (a -> m) -> {ix: Ix} -> PData d a ix -> m
    gconcatMap d constraints f (Con x) = assert_total $ gconcatMapd d constraints d constraints f x
