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

mutual
  gleqdTotal : {e, Ix: _} -> (dr: TaggedDesc e Ix) -> (constraintsr: TaggedConstraints SOrd dr) -> (d: Desc Ix) -> (constraints: Constraints SOrd d) -> {ix: Ix} -> (X: Synthesize d (TaggedData dr) ix) -> (Y: Synthesize d (TaggedData dr) ix) -> Either (So (gleqd dr constraintsr d constraints X Y)) (So (gleqd dr constraintsr d constraints Y X))
  gleqdTotal dr constraintsr (Ret ix) constraints Refl Refl = Left Oh
  gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) with (choose (a1 <= a2))
    gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) | (Left l) with (choose (a2 <= a1))
      gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) | (Left l) | (Left x) with (leqAntisymmetricReflective {x = a1} {y = a2} l x)
        gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) | (Left l) | (Left x) | Refl with (assert_total $ gleqdTotal dr constraintsr (kdesc a) (sordr a) r1 r2)
          gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) | (Left l) | (Left x) | Refl | (Left y) = Left y
          gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) | (Left l) | (Left x) | Refl | (Right r) with (choose (a <= a))
            gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) | (Left l) | (Left x) | Refl | (Right r) | (Left y) with (leqAntisymmetricReflective {x = a} {y = a} x y)
              gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) | (Left l) | (Left x) | Refl | (Right r) | (Left y) | Refl with (assert_total $ gleqdTotal dr constraintsr (kdesc a) (sordr a) r1 r2)
                gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) | (Left l) | (Left x) | Refl | (Right r) | (Left y) | Refl | (Left z) = Left z
                gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) | (Left l) | (Left x) | Refl | (Right r) | (Left y) | Refl | (Right z) = Right z
            gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) | (Left l) | (Left x) | Refl | (Right r) | (Right y) = void (soNotSo x y)
      gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) | (Left l) | (Right r) = Left Oh
    gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) | (Right r) with (choose (a2 <= a1))
      gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) | (Right r) | (Left l) with (choose (a1 <= a2))
        gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) | (Right r) | (Left l) | (Left x) with (leqAntisymmetricReflective {x = a2} {y = a1} l x)
          gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) | (Right r) | (Left l) | (Left x) | Refl = void (soNotSo l r)
        gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) | (Right r) | (Left l) | (Right x) = Right Oh
      gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) | (Right r) | (Right x) with (leqTotal {x = a1} {y = a2})
        gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) | (Right r) | (Right x) | (Left l) = void (soNotSo l r)
        gleqdTotal dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) | (Right r) | (Right x) | (Right y) = void (soNotSo y x)
  gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) with (gleqTotal dr constraintsr ra1 ra2)
    gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | (Left l) with (gleqdTotal dr constraintsr kdesc constraints r1 r2)
      gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | (Left l) | (Left x) = rewrite soToEq l in Left x
      gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | (Left l) | (Right r) = ?rhs_2
    gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | (Right r) = ?gleqdTotal_rhs_2

  gleqTotal : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints SOrd d) -> {ix: Ix} -> (X: TaggedData d ix) -> (Y: TaggedData d ix) -> Either (So (gleq d constraints X Y)) (So (gleq d constraints Y X))
