module Descriptions.Foldable

import Descriptions.Core

%default total
%access export
%auto_implicits off

using (m: Type)
  mutual
    gconcatMapd : Monoid m => {a, e, Ix: _} -> (dr: PTaggedDesc e (S Z) Ix) -> PTaggedConstraints1 Foldable dr
                                         -> (d: PDesc (S Z) Ix) -> PConstraints1 Foldable d
                                         -> (a -> m) -> {ix: Ix} -> PSynthesize d a (PTaggedData dr a) ix -> m
    gconcatMapd dr constraintsr (PRet ix) constraints f Refl = neutral
    gconcatMapd dr constraintsr (PArg A kdesc) constraints f (arg ** rest) = gconcatMapd dr constraintsr (kdesc arg) (constraints arg) f rest
    gconcatMapd dr constraintsr (PPar FZ kdesc) constraints f (par ** rest) = f par <+> gconcatMapd dr constraintsr kdesc constraints f rest
    gconcatMapd _ _ (PPar (FS FZ) _) _ _ _ impossible
    gconcatMapd _ _ (PPar (FS (FS _)) _) _ _ _ impossible
    gconcatMapd dr constraintsr (PMap g FZ kdesc) (foldable, constraints) f (targ ** rest) =
      concatMap @{foldable} f targ <+> gconcatMapd dr constraintsr kdesc constraints f rest
    gconcatMapd _ _ (PMap _ (FS FZ) _) _ _ _ impossible
    gconcatMapd _ _ (PMap _ (FS (FS _)) _) _ _ _ impossible
    gconcatMapd dr constraintsr (PRec ix kdesc) constraints f (rec ** rest) =
      gconcatMap dr constraintsr f rec <+> gconcatMapd dr constraintsr kdesc constraints f rest

    gconcatMap : Monoid m => {a, e, Ix: _} -> (d: PTaggedDesc e (S Z) Ix) -> PTaggedConstraints1 Foldable d -> (a -> m) -> {ix: Ix} -> PTaggedData d a ix -> m
    gconcatMap d constraints f (Con (l ** t ** r)) = assert_total $ gconcatMapd d constraints (d l t) (constraints l t) f r
