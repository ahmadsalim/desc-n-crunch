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

compareTagsReflective : {e,l : _} -> (t : Tag l e) -> compareTags t t = Left Refl
compareTagsReflective Z = Refl
compareTagsReflective (S x) with (compareTagsReflective x)
  compareTagsReflective (S x) | res = rewrite res in Refl


mutual
  gleqdReflexive : {e, Ix: _} -> (dr: TaggedDesc e Ix) -> (constraintsr: TaggedConstraints SOrd dr) -> (d: Desc Ix) -> (constraints: Constraints SOrd d) -> {ix: Ix} -> (X: Synthesize d (TaggedData dr) ix) -> So (gleqd dr constraintsr d constraints X X)
  gleqdReflexive dr constraintsr (Ret ix) constraints Refl = Oh
  gleqdReflexive dr constraintsr (Arg A kdesc) (sorda, sordr) (arg ** rest) with (choose (arg <= arg))
    gleqdReflexive dr constraintsr (Arg A kdesc) (sorda, sordr) (arg ** rest) | (Left l) with (choose (arg <= arg)) -- why do we need to do this again?
      gleqdReflexive dr constraintsr (Arg A kdesc) (sorda, sordr) (arg ** rest) | (Left l) | (Left x) with (leqAntisymmetricReflective {x = arg} {y = arg} l x)
        gleqdReflexive dr constraintsr (Arg A kdesc) (sorda, sordr) (arg ** rest) | (Left l) | (Left x) | Refl =
          assert_total $ gleqdReflexive dr constraintsr (kdesc arg) (sordr arg) rest
      gleqdReflexive dr constraintsr (Arg A kdesc) (sorda, sordr) (arg ** rest) | (Left l) | (Right r) = Oh -- This seems counter-intuitive but looks true-ish
    gleqdReflexive dr constraintsr (Arg A kdesc) (sorda, sordr) (arg ** rest) | (Right r) = void (soNotSo (leqReflexive {x = arg}) r)
  gleqdReflexive dr constraintsr (Rec ix kdesc) constraints (rec ** rest) with (assert_total $ gleqReflexive dr constraintsr rec)
    gleqdReflexive dr constraintsr (Rec ix kdesc) constraints (rec ** rest) | recleqrefl = rewrite soToEq recleqrefl in gleqdReflexive dr constraintsr kdesc constraints rest
  gleqReflexive : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints SOrd d) -> {ix: Ix} -> (X: TaggedData d ix) -> So (gleq d constraints X X)
  gleqReflexive d constraints (Con (l ** t ** r)) with (compareTags t t) proof cptag
    gleqReflexive d constraints (Con (l ** t ** r)) | (Left Refl) = gleqdReflexive d constraints (d l t) (constraints l t) r
    gleqReflexive d constraints (Con (l ** t ** r)) | (Right x) with (compareTagsReflective t)
      gleqReflexive d constraints (Con (l ** t ** r)) | (Right x) | cptagrefl =
        (\Refl impossible) (trans cptag cptagrefl)

