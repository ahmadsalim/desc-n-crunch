module Descriptions.Ord

import Interfaces
import Descriptions.Core

%default total
%access export
%auto_implicits off

compareTags : {e, l, l' : _} -> (t1 : Tag l e) -> (t2 : Tag l' e) -> Either (t1 = t2) Bool
compareTags Z Z = Left Refl
compareTags Z (S x) = Right True
compareTags (S x) Z = Right False
compareTags (S x) (S y) with (compareTags x y)
  compareTags (S y) (S y) | (Left Refl) = Left Refl
  compareTags (S x) (S y) | (Right r) = Right r

mutual
  gleqd : {e, Ix: _} -> (dr: TaggedDesc e Ix) -> (constraintsr: TaggedConstraints SOrd dr) -> (d: Desc Ix) -> (constraints: Constraints SOrd d) -> {ix: Ix} -> (X: Synthesize d (TaggedData dr) ix) -> (Y: Synthesize d (TaggedData dr) ix) -> Bool
  gleqd dr constraintsr (Ret ix) constraints Refl Refl = True
  gleqd dr constraintsr (Arg A kdesc) (orda, ordr) (a1 ** r1) (a2 ** r2) with (choose (a1 <= a2))
    gleqd dr constraintsr (Arg A kdesc) (orda, ordr) (a1 ** r1) (a2 ** r2) | (Left l) with (choose (a2 <= a1))
      gleqd dr constraintsr (Arg A kdesc) (orda, ordr) (a1 ** r1) (a2 ** r2) | (Left l) | (Left l') with (leqAntisymmetricReflective {x = a1} {y = a2} l l')
          gleqd dr constraintsr (Arg A kdesc) (orda, ordr) (a ** r1) (a ** r2) | (Left l) | (Left l') | Refl = assert_total $ gleqd dr constraintsr (kdesc a) (ordr a) r1 r2
      gleqd dr constraintsr (Arg A kdesc) (orda, ordr) (a1 ** r1) (a2 ** r2) | (Left l) | (Right r) = True
    gleqd dr constraintsr (Arg A kdesc) (orda, ordr) (a1 ** r1) (a2 ** r2) | (Right r) = False
  gleqd dr constraintsr (Rec ix kdesc) constraints (x1 ** r1) (x2 ** r2) = assert_total $ gleq dr constraintsr x1 x2 && gleqd dr constraintsr kdesc constraints r1 r2

  gleq : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints SOrd d) -> {ix: Ix} -> (X : TaggedData d ix) -> (Y : TaggedData d ix) -> Bool
  gleq d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) with (compareTags t1 t2)
    gleq d constraints (Con (l ** t ** r1)) (Con (l ** t ** r2)) | (Left Refl) = gleqd d constraints (d l t) (constraints l t) r1 r2
    gleq d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) | (Right r) = r


