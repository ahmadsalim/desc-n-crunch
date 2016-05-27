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
  gleqd dr constraintsr (Rec ix kdesc) constraints (x1 ** r1) (x2 ** r2) with (assert_total $ gleq dr constraintsr x1 x2)
    gleqd dr constraintsr (Rec ix kdesc) constraints (x1 ** r1) (x2 ** r2) | False = False
    gleqd dr constraintsr (Rec ix kdesc) constraints (x1 ** r1) (x2 ** r2) | True with (assert_total $ gleq dr constraintsr x2 x1)
      gleqd dr constraintsr (Rec ix kdesc) constraints (x1 ** r1) (x2 ** r2) | True | False = True
      gleqd dr constraintsr (Rec ix kdesc) constraints (x1 ** r1) (x2 ** r2) | True | True = gleqd dr constraintsr kdesc constraints r1 r2



  gleq : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints SOrd d) -> {ix: Ix} -> (X : TaggedData d ix) -> (Y : TaggedData d ix) -> Bool
  gleq d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) with (compareTags t1 t2)
    gleq d constraints (Con (l ** t ** r1)) (Con (l ** t ** r2)) | (Left Refl) = gleqd d constraints (d l t) (constraints l t) r1 r2
    gleq d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) | (Right r) = r

compareTagsReflective : {e,l : _} -> (t : Tag l e) -> compareTags t t = Left Refl
compareTagsReflective Z = Refl
compareTagsReflective (S x) with (compareTagsReflective x)
  compareTagsReflective (S x) | res = rewrite res in Refl

compareTagsRightUnequal : {e, l, l', v : _} -> (t : Tag l e) -> (t' : Tag l' e) -> (compareTags t t' = Right v) -> (t = t') -> Void
compareTagsRightUnequal Z Z Refl _ impossible
compareTagsRightUnequal Z (S _) _ Refl impossible
compareTagsRightUnequal (S _) Z _ Refl impossible
compareTagsRightUnequal (S x) (S x) prf Refl with (trans (sym $ compareTagsReflective (S x)) prf)
  compareTagsRightUnequal (S _) (S _) _ Refl | Refl impossible

compareTagsRightFRightFVoid : {e, l, l2, v : _} -> (t : Tag l e) -> (t2 : Tag l2 e) -> (compareTags t t2 = Right v) -> (compareTags t2 t = Right v) -> Void
compareTagsRightFRightFVoid {v = False} Z Z Refl _ impossible
compareTagsRightFRightFVoid {v = False} Z (S _) Refl _ impossible
compareTagsRightFRightFVoid {v = False} (S _) Z _ Refl impossible
compareTagsRightFRightFVoid {v = False} (S x) (S y) prf prf1 with (compareTags x y) proof xleqy
  compareTagsRightFRightFVoid {v = False} (S _) (S _) Refl _ | (Left Refl) impossible
  compareTagsRightFRightFVoid {v = False} (S x) (S y) prf prf1 | (Right False) with (compareTags y x) proof yleqx
    compareTagsRightFRightFVoid {v = False} (S _) (S _) _ Refl | (Right False) | (Left Refl) impossible
    compareTagsRightFRightFVoid {v = False} (S x) (S y) prf prf1 | (Right False) | (Right False) = compareTagsRightFRightFVoid {v = False} x y (sym xleqy) (sym yleqx)
    compareTagsRightFRightFVoid {v = False} (S _) (S _) _ Refl | (Right False) | (Right True) impossible
  compareTagsRightFRightFVoid {v = False} (S _) (S _) Refl _ | (Right True) impossible
compareTagsRightFRightFVoid {v = True} Z Z Refl _ impossible
compareTagsRightFRightFVoid {v = True} Z (S _) _ Refl impossible
compareTagsRightFRightFVoid {v = True} (S _) Z Refl _ impossible
compareTagsRightFRightFVoid {v = True} (S x) (S y) prf prf1 with (compareTags x y) proof xleqy
  compareTagsRightFRightFVoid {v = True} (S _) (S _) Refl _ | (Left Refl) impossible
  compareTagsRightFRightFVoid {v = True} (S _) (S _) Refl _ | (Right False) impossible
  compareTagsRightFRightFVoid {v = True} (S x) (S y) prf prf1 | (Right True) with (compareTags y x) proof yleqx
    compareTagsRightFRightFVoid {v = True} (S _) (S _) _ Refl | (Right True) | (Left Refl) impossible
    compareTagsRightFRightFVoid {v = True} (S _) (S _) _ Refl | (Right True) | (Right False) impossible
    compareTagsRightFRightFVoid {v = True} (S x) (S y) prf prf1 | (Right True) | (Right True) = compareTagsRightFRightFVoid {v = True} x y (sym xleqy) (sym yleqx)

compareTagsTransitive : (t1,t2,t3: _) -> compareTags t1 t3 = Right True -> compareTags t3 t2 = Right True -> compareTags t1 t2 = Right True
compareTagsTransitive Z _ Z Refl _ impossible
compareTagsTransitive Z Z (S _) _ Refl impossible
compareTagsTransitive Z (S y) (S x) prf prf1 with (compareTags x y) proof cxy
  compareTagsTransitive Z (S _) (S _) _ Refl | (Left Refl) impossible
  compareTagsTransitive Z (S y) (S x) prf prf1 | (Right False) = Refl
  compareTagsTransitive Z (S y) (S x) prf prf1 | (Right True) = Refl
compareTagsTransitive (S _) Z Z _ Refl impossible
compareTagsTransitive (S _) Z (S _) _ Refl impossible
compareTagsTransitive (S x) (S y) t3 prf prf1 with (compareTags x y) proof cxy
  compareTagsTransitive (S _) (S _) Z Refl _ | (Left Refl) impossible
  compareTagsTransitive (S y) (S y) (S x) prf prf1 | (Left Refl) with (compareTags y x) proof cyx
    compareTagsTransitive (S _) (S _) (S _) Refl _ | (Left Refl) | (Left Refl) impossible
    compareTagsTransitive (S _) (S _) (S _) Refl _ | (Left Refl) | (Right False) impossible
    compareTagsTransitive (S y) (S y) (S x) prf prf1 | (Left Refl) | (Right True) with (compareTags x y) proof cxy'
      compareTagsTransitive (S _) (S _) (S _) _ Refl | (Left Refl) | (Right True) | (Left Refl) impossible
      compareTagsTransitive (S _) (S _) (S _) _ Refl | (Left Refl) | (Right True) | (Right False) impossible
      compareTagsTransitive (S y) (S y) (S x) prf prf1 | (Left Refl) | (Right True) | (Right True) with (compareTagsTransitive y y x (sym cyx) (sym cxy'))
        compareTagsTransitive (S y) (S y) (S x) prf prf1 | (Left Refl) | (Right True) | (Right True) | prf2 = case trans cxy prf2 of Refl impossible
  compareTagsTransitive (S _) (S _) Z Refl _ | (Right False) impossible
  compareTagsTransitive (S x) (S y) (S z) prf prf1 | (Right False) with (compareTags x z) proof cxz
    compareTagsTransitive (S _) (S _) (S _) Refl _ | (Right False) | (Left Refl) impossible
    compareTagsTransitive (S _) (S _) (S _) Refl _ | (Right False) | (Right False) impossible
    compareTagsTransitive (S x) (S y) (S z) prf prf1 | (Right False) | (Right True) with (compareTags z y) proof czy
      compareTagsTransitive (S _) (S _) (S _) _ Refl | (Right False) | (Right True) | (Left Refl) impossible
      compareTagsTransitive (S _) (S _) (S _) _ Refl | (Right False) | (Right True) | (Right False) impossible
      compareTagsTransitive (S x) (S y) (S z) prf prf1 | (Right False) | (Right True) | (Right True) with (compareTagsTransitive x y z (sym cxz) (sym czy))
        compareTagsTransitive (S x) (S y) (S z) prf prf1 | (Right False) | (Right True) | (Right True) | prf2 = case trans cxy prf2 of Refl impossible
  compareTagsTransitive (S x) (S y) t3 prf prf1 | (Right True) = Refl

mutual
  gleqdReflexive : {e, Ix: _} -> (dr: TaggedDesc e Ix) -> (constraintsr: TaggedConstraints SOrd dr) -> (d: Desc Ix) -> (constraints: Constraints SOrd d) -> {ix: Ix} -> (X: Synthesize d (TaggedData dr) ix) -> So (gleqd dr constraintsr d constraints X X)
  gleqdReflexive dr constraintsr (Ret ix) constraints Refl = Oh
  gleqdReflexive dr constraintsr (Arg A kdesc) (sorda, sordr) (arg ** rest) with (choose (arg <= arg))
    gleqdReflexive dr constraintsr (Arg A kdesc) (sorda, sordr) (arg ** rest) | (Left l) with (choose (arg <= arg)) -- why do we need to do this again
      gleqdReflexive dr constraintsr (Arg A kdesc) (sorda, sordr) (arg ** rest) | (Left l) | (Left x) with (leqAntisymmetricReflective {x = arg} {y = arg} l x)
        gleqdReflexive dr constraintsr (Arg A kdesc) (sorda, sordr) (arg ** rest) | (Left l) | (Left x) | Refl =
          assert_total $ gleqdReflexive dr constraintsr (kdesc arg) (sordr arg) rest
      gleqdReflexive dr constraintsr (Arg A kdesc) (sorda, sordr) (arg ** rest) | (Left l) | (Right r) = Oh -- This seems counter-intuitive but looks true-ish
    gleqdReflexive dr constraintsr (Arg A kdesc) (sorda, sordr) (arg ** rest) | (Right r) = void (soNotSo (leqReflexive {x = arg}) r)
  gleqdReflexive dr constraintsr (Rec ix kdesc) constraints (rec ** rest) with (assert_total $ gleqReflexive dr constraintsr rec)
    gleqdReflexive dr constraintsr (Rec ix kdesc) constraints (rec ** rest) | recleqrefl =
      rewrite soToEq recleqrefl in rewrite soToEq recleqrefl in gleqdReflexive dr constraintsr kdesc constraints rest
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
  gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) with (gleq dr constraintsr ra1 ra2) proof ra1leqra2
    gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | False with (gleq dr constraintsr ra2 ra1) proof ra2leqra1
      gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | False | False with (assert_total $ gleqTotal dr constraintsr ra1 ra2)
        gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | False | False | (Left l) with (trans ra1leqra2 (soToEq l))
          gleqdTotal _ _ (Rec _ _) _ (_ ** _) (_ ** _) | False | False | (Left _) | Refl impossible
        gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | False | False | (Right r) with (trans ra2leqra1 (soToEq r))
          gleqdTotal _ _ (Rec _ _) _ (_ ** _) (_ ** _) | False | False | (Right _) | Refl impossible
      gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | False | True with (gleqd dr constraintsr kdesc constraints r2 r1) proof r2leqr1
        gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | False | True | False = rewrite sym ra1leqra2 in Right Oh
        gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | False | True | True = rewrite sym ra1leqra2 in Right Oh
    gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | True with (gleq dr constraintsr ra2 ra1) proof ra2leqra1
      gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | True | False = Left Oh
      gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | True | True with (gleqd dr constraintsr kdesc constraints r1 r2) proof r1leqr2
        gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | True | True | False with (gleqd dr constraintsr kdesc constraints r2 r1) proof r2leqr1
          gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | True | True | False | False with (assert_total $ gleqdTotal dr constraintsr kdesc constraints r1 r2)
            gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | True | True | False | False | (Left l) with (trans r1leqr2 (soToEq l))
              gleqdTotal _ _ (Rec _ _) _ (_ ** _) (_ ** _) | True | True | False | False | (Left _) | Refl impossible
            gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | True | True | False | False | (Right r) with (trans r2leqr1 (soToEq r))
              gleqdTotal _ _ (Rec _ _) _ (_ ** _) (_ ** _) | True | True | False | False | (Right _) | Refl impossible
          gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | True | True | False | True = rewrite sym ra1leqra2 in rewrite sym r2leqr1 in Right Oh
        gleqdTotal dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) | True | True | True = Left Oh
  gleqTotal : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints SOrd d) -> {ix: Ix} -> (X: TaggedData d ix) -> (Y: TaggedData d ix) -> Either (So (gleq d constraints X Y)) (So (gleq d constraints Y X))
  gleqTotal d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) with (compareTags t1 t2) proof t1leqt2
    gleqTotal d constraints (Con (l ** t ** r1)) (Con (l ** t ** r2)) | (Left Refl) = rewrite compareTagsReflective t in gleqdTotal d constraints (d l t) (constraints l t) r1 r2
    gleqTotal d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) | (Right False) with (compareTags t2 t1) proof t2leqt1
      gleqTotal d constraints (Con (l ** t ** r1)) (Con (l ** t ** r2)) | (Right False) | (Left Refl) = void (compareTagsRightUnequal t t (sym t1leqt2) Refl)
      gleqTotal d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) | (Right False) | (Right False) = void (compareTagsRightFRightFVoid t1 t2 (sym t1leqt2) (sym t2leqt1))
      gleqTotal d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) | (Right False) | (Right True) = Right Oh
    gleqTotal d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) | (Right True) = Left Oh

mutual
  gleqdAntisymmetricReflecive : {e, Ix: _} -> (dr: TaggedDesc e Ix) -> (constraintsr: TaggedConstraints SOrd dr) -> (d : Desc Ix) -> (constraints: Constraints SOrd d) -> {ix : Ix} -> (X: Synthesize d (TaggedData dr) ix) -> (Y: Synthesize d (TaggedData dr) ix) -> So (gleqd dr constraintsr d constraints X Y) -> So (gleqd dr constraintsr d constraints Y X) -> X = Y
  gleqdAntisymmetricReflecive dr constraintsr (Ret ix) constraints Refl Refl xleqy yleqx = Refl
  gleqdAntisymmetricReflecive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) xleqy yleqx with (choose (a1 <= a2))
    gleqdAntisymmetricReflecive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) xleqy yleqx | (Left l) with (choose (a2 <= a1))
      gleqdAntisymmetricReflecive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) xleqy yleqx | (Left l) | (Left x) with (leqAntisymmetricReflective {x = a1} {y = a2} l x)
        gleqdAntisymmetricReflecive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) xleqy yleqx | (Left l) | (Left x) | Refl with (choose (gleqd dr constraintsr (kdesc a) (sordr a) r1 r2))
          gleqdAntisymmetricReflecive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) xleqy yleqx | (Left l) | (Left x) | Refl | Left y with (choose (a <= a))
            gleqdAntisymmetricReflecive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) xleqy yleqx | (Left l) | (Left x) | Refl | Left y | (Left z) with (leqAntisymmetricReflective {x = a} {y = a} x z)
              gleqdAntisymmetricReflecive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) xleqy yleqx | (Left l) | (Left x) | Refl | Left y | (Left z) | Refl with (assert_total $ gleqdAntisymmetricReflecive dr constraintsr (kdesc a) (sordr a) r1 r2 xleqy yleqx)
                gleqdAntisymmetricReflecive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r) (a ** r) xleqy yleqx | (Left l) | (Left x) | Refl | Left y | (Left z) | Refl | Refl = Refl
            gleqdAntisymmetricReflecive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) xleqy yleqx | (Left l) | (Left x) | Refl | Left y | (Right r) = void (soNotSo x r)
          gleqdAntisymmetricReflecive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) xleqy yleqx | (Left l) | (Left x) | Refl | Right y = void (soNotSo xleqy y)
      gleqdAntisymmetricReflecive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) xleqy yleqx | (Left l) | (Right r) = case yleqx of Oh impossible
    gleqdAntisymmetricReflecive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) xleqy yleqx | (Right r) = case xleqy of Oh impossible
  gleqdAntisymmetricReflecive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) xleqy yleqx with (gleq dr constraintsr ra1 ra2) proof ra1leqra2
    gleqdAntisymmetricReflecive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) xleqy yleqx | True with (gleq dr constraintsr ra2 ra1) proof ra2leqra1
      gleqdAntisymmetricReflecive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) xleqy yleqx | True | False = case yleqx of Oh impossible
      gleqdAntisymmetricReflecive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) xleqy yleqx | True | True with (gleq dr constraintsr ra1 ra2) proof ra1leqra2'
        gleqdAntisymmetricReflecive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) xleqy yleqx | True | True | False = case ra1leqra2 of Refl impossible
        gleqdAntisymmetricReflecive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) xleqy yleqx | True | True | True with (assert_total $ gleqdAntisymmetricReflecive dr constraintsr kdesc constraints r1 r2 xleqy yleqx)
          gleqdAntisymmetricReflecive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r2) (ra2 ** r2) xleqy yleqx | True | True | True | Refl with (gleqAntisymmetricReflecive dr constraintsr ra1 ra2 (eqToSo $ sym ra1leqra2') (eqToSo $ sym ra2leqra1))
            gleqdAntisymmetricReflecive dr constraintsr (Rec ix kdesc) constraints (ra ** r) (ra ** r) xleqy yleqx | True | True | True | Refl | Refl = Refl

    gleqdAntisymmetricReflecive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) xleqy yleqx | False = case xleqy of Oh impossible
  gleqAntisymmetricReflecive : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints SOrd d) -> {ix : Ix} -> (X: TaggedData d ix) -> (Y: TaggedData d ix) -> So (gleq d constraints X Y) -> So (gleq d constraints Y X) -> X = Y
  gleqAntisymmetricReflecive d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) xleqy yleqx with (compareTags t1 t2) proof t1leqt2
    gleqAntisymmetricReflecive d constraints (Con (l ** t ** r1)) (Con (l ** t ** r2)) xleqy yleqx | (Left Refl) with (compareTags t t) proof tleqt
      gleqAntisymmetricReflecive d constraints (Con (l ** t ** r1)) (Con (l ** t ** r2)) xleqy yleqx | (Left Refl) | (Left Refl) with (assert_total $ gleqdAntisymmetricReflecive d constraints (d l t) (constraints l t) r1 r2 xleqy yleqx)
        gleqAntisymmetricReflecive d constraints (Con (l ** t ** r)) (Con (l ** t ** r)) xleqy yleqx | (Left Refl) | (Left Refl) | Refl = Refl
      gleqAntisymmetricReflecive d constraints (Con (l ** t ** r1)) (Con (l ** t ** r2)) xleqy yleqx | (Left Refl) | (Right r) = case t1leqt2 of Refl impossible
    gleqAntisymmetricReflecive d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) xleqy yleqx | (Right False) = case xleqy of Oh impossible
    gleqAntisymmetricReflecive d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) xleqy yleqx | (Right True) with (compareTags t2 t1) proof t2leqt1
      gleqAntisymmetricReflecive d constraints (Con (l1 ** t1 ** r1)) (Con (l1 ** t1 ** r2)) xleqy yleqx | (Right True) | (Left Refl) = case trans t1leqt2 (sym t2leqt1) of Refl impossible
      gleqAntisymmetricReflecive d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) xleqy yleqx | (Right True) | (Right False) = case yleqx of Oh impossible
      gleqAntisymmetricReflecive d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) xleqy yleqx | (Right True) | (Right True) =
          void (compareTagsRightFRightFVoid t1 t2 (sym t1leqt2) (sym t2leqt1))

mutual
  gleqdTransitive : {e, Ix: _} -> (dr: TaggedDesc e Ix) -> (constraintsr: TaggedConstraints SOrd dr) -> (d: Desc Ix) -> (constraints: Constraints SOrd d) -> {ix : Ix} -> (x: Synthesize d (TaggedData dr) ix) -> (y: Synthesize d (TaggedData dr) ix) -> (z: Synthesize d (TaggedData dr) ix) -> So (gleqd dr constraintsr d constraints x z) -> So (gleqd dr constraintsr d constraints z y) -> So (gleqd dr constraintsr d constraints x y)
  gleqdTransitive dr constraintsr (Ret ix) constraints Refl Refl Refl xleqz zleqy = Oh
  gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy with (choose (a1 <= a2))
    gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | (Left l) with (choose (a2 <= a1))
      gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | (Left l) | (Left x) with (leqAntisymmetricReflective {x = a1} {y = a2} l x)
        gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | (Left l) | (Left x) | Refl with (choose (a <= a3))
          gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | (Left l) | (Left x) | Refl | (Left y) with (choose (a3 <= a))
            gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | (Left l) | (Left x) | Refl | (Left y) | (Left z) with (choose (a <= a3))
              gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | (Left l) | (Left x) | Refl | (Left y) | (Left z) | (Left w) with (leqAntisymmetricReflective {x = a} {y = a3} w z)
                gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) (a ** r3) xleqz zleqy | (Left l) | (Left x) | Refl | (Left y) | (Left z) | (Left w) | Refl with (leqAntisymmetricReflective {x = a} {y = a} y z)
                  gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) (a ** r3) xleqz zleqy | (Left l) | (Left x) | Refl | (Left y) | (Left z) | (Left w) | Refl | Refl with (leqAntisymmetricReflective {x = a} {y = a} z w)
                    gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) (a ** r3) xleqz zleqy | (Left l) | (Left x) | Refl | (Left y) | (Left z) | (Left w) | Refl | Refl | Refl = assert_total $ gleqdTransitive dr constraintsr (kdesc a) (sordr a) r1 r2 r3 xleqz zleqy
              gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | (Left l) | (Left x) | Refl | (Left y) | (Left z) | (Right r) = void (soNotSo y r)
            gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | (Left l) | (Left x) | Refl | (Left y) | (Right r) = case zleqy of Oh impossible
          gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | (Left l) | (Left x) | Refl | (Right r) = case xleqz of Oh impossible
      gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | (Left l) | (Right r) = Oh
    gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | (Right r) with (choose (a1 <= a3))
      gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | (Right r) | (Left l) with (choose (a3 <= a2))
        gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | (Right r) | (Left l) | (Left x) with (leqTransitive {x = a1} {z = a3} {y = a2} l x)
          gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | (Right r) | (Left l) | (Left x) | a1leqa2 = void (soNotSo a1leqa2 r)
        gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | (Right r) | (Left l) | (Right x) = case zleqy of Oh impossible
      gleqdTransitive dr constraintsr (Arg A kdesc) (sorda, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | (Right r) | (Right x) = case xleqz of Oh impossible
  gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy with (gleq dr constraintsr ra1 ra2) proof ra1leqra2
    gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False with (gleq dr constraintsr ra1 ra3) proof ra1leqra3
      gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | False = case xleqz of Oh impossible
      gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True with (gleq dr constraintsr ra3 ra1) proof ra3leqra1
        gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | False with (gleq dr constraintsr ra3 ra2) proof ra3leqra2
          gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | False | False = case zleqy of Oh impossible
          gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | False | True with (gleq dr constraintsr ra2 ra3) proof ra2leqra3
            gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | False | True | False with (gleqTransitive dr constraintsr ra1 ra2 ra3 (eqToSo $ sym ra1leqra3) (eqToSo $ sym ra3leqra2))
              gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | False | True | False | prf = case trans ra1leqra2 (soToEq prf) of Refl impossible
            gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | False | True | True with (gleqTransitive dr constraintsr ra1 ra2 ra3 (eqToSo $ sym ra1leqra3) (eqToSo $ sym ra3leqra2))
              gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | False | True | True | prf = case trans ra1leqra2 (soToEq prf) of Refl impossible
        gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | True with (gleq dr constraintsr ra3 ra2) proof ra3leqra2
          gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | True | False = case zleqy of Oh impossible
          gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | True | True with (gleqTransitive dr constraintsr ra1 ra2 ra3 (eqToSo $ sym ra1leqra3) (eqToSo $ sym ra3leqra2))
            gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | True | True | prf = case trans ra1leqra2 (soToEq $ prf) of Refl impossible
    gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True with (gleq dr constraintsr ra2 ra1) proof ra2leqra1
      gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | False = Oh
      gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True with (gleq dr constraintsr ra1 ra3) proof ra1leqra3
        gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | False = case xleqz of Oh impossible
        gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True with (gleq dr constraintsr ra3 ra1) proof ra3leqra1
          gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | False with (gleq dr constraintsr ra3 ra2) proof ra3leqra2
            gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | False | False = case zleqy of Oh impossible
            gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | False | True with (gleq dr constraintsr ra2 ra3) proof ra2leqra3
              gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | False | True | False with (gleqTransitive dr constraintsr ra3 ra1 ra2 (eqToSo $ sym ra3leqra2) (eqToSo $ sym ra2leqra1))
                gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | False | True | False | prf = case trans (ra3leqra1) (soToEq prf) of Refl impossible
              gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | False | True | True with (gleqTransitive dr constraintsr ra3 ra1 ra2 (eqToSo $ sym ra3leqra2) (eqToSo $ sym ra2leqra1))
                gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | False | True | True | prf = case trans (ra3leqra1) (soToEq prf) of Refl impossible
          gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | True with (gleq dr constraintsr ra3 ra2) proof ra3leqra2
            gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | True | False = case zleqy of Oh impossible
            gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | True | True with (gleq dr constraintsr ra2 ra3) proof ra2leqra3
              gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | True | True | False with (gleqTransitive dr constraintsr ra2 ra3 ra1 (eqToSo $ sym ra2leqra1) (eqToSo $ sym ra1leqra3))
                gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | True | True | False | prf = case trans ra2leqra3 (soToEq prf) of Refl impossible
              gleqdTransitive dr constraintsr (Rec ix kdesc) constraints (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | True | True | True = gleqdTransitive dr constraintsr kdesc constraints r1 r2 r3 xleqz zleqy

  gleqTransitive : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints SOrd d) -> {ix : Ix} -> (x: TaggedData d ix) -> (y: TaggedData d ix) -> (z: TaggedData d ix) -> So (gleq d constraints x z) -> So (gleq d constraints z y) -> So (gleq d constraints x y)
  gleqTransitive d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) (Con (l3 ** t3 ** r3)) xleqz zleqy with (compareTags t1 t3) proof ct1t3
    gleqTransitive d constraints (Con (l ** t ** r1)) (Con (l2 ** t2 ** r2)) (Con (l ** t ** r3)) xleqz zleqy | (Left Refl) with (compareTags t t2) proof ctt2
      gleqTransitive d constraints (Con (l ** t ** r1)) (Con (l ** t ** r2)) (Con (l ** t ** r3)) xleqz zleqy | (Left Refl) | (Left Refl) = assert_total $ gleqdTransitive d constraints (d l t) (constraints l t) r1 r2 r3 xleqz zleqy
      gleqTransitive d constraints (Con (l ** t ** r1)) (Con (l2 ** t2 ** r2)) (Con (l ** t ** r3)) xleqz zleqy | (Left Refl) | (Right r) = zleqy
    gleqTransitive d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) (Con (l3 ** t3 ** r3)) xleqz zleqy | (Right False) = case xleqz of Oh impossible
    gleqTransitive d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) (Con (l3 ** t3 ** r3)) xleqz zleqy | (Right True) with (compareTags t3 t2) proof ct3t2
      gleqTransitive d constraints (Con (l1 ** t1 ** r1)) (Con (l ** t ** r2)) (Con (l ** t ** r3)) xleqz zleqy | (Right True) | (Left Refl) with (compareTags t1 t) proof ct1t
        gleqTransitive d constraints (Con (l ** t ** r1)) (Con (l ** t ** r2)) (Con (l ** t ** r3)) xleqz zleqy | (Right True) | (Left Refl) | (Left Refl) = case ct1t3 of Refl impossible
        gleqTransitive d constraints (Con (l1 ** t1 ** r1)) (Con (l ** t ** r2)) (Con (l ** t ** r3)) xleqz zleqy | (Right True) | (Left Refl) | (Right False) = case ct1t3 of Refl impossible
        gleqTransitive d constraints (Con (l1 ** t1 ** r1)) (Con (l ** t ** r2)) (Con (l ** t ** r3)) xleqz zleqy | (Right True) | (Left Refl) | (Right True) = Oh
      gleqTransitive d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) (Con (l3 ** t3 ** r3)) xleqz zleqy | (Right True) | (Right False) = case zleqy of Oh impossible
      gleqTransitive d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) (Con (l3 ** t3 ** r3)) xleqz zleqy | (Right True) | (Right True) with (compareTags t1 t2) proof ct1t2
        gleqTransitive d constraints (Con (l ** t ** r1)) (Con (l ** t ** r2)) (Con (l3 ** t3 ** r3)) xleqz zleqy | (Right True) | (Right True) | (Left Refl) = void (compareTagsRightFRightFVoid t t3 (sym ct1t3) (sym ct3t2))
        gleqTransitive d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) (Con (l3 ** t3 ** r3)) xleqz zleqy | (Right True) | (Right True) | (Right False) with (compareTagsTransitive t1 t2 t3 (sym ct1t3) (sym ct3t2))
          gleqTransitive d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) (Con (l3 ** t3 ** r3)) xleqz zleqy | (Right True) | (Right True) | (Right False) | prf = case trans ct1t2 prf of Refl impossible
        gleqTransitive d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) (Con (l3 ** t3 ** r3)) xleqz zleqy | (Right True) | (Right True) | (Right True) = Oh

