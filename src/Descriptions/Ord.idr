module Descriptions.Ord

import Helper
import Interfaces
import Descriptions.Core

%default total
%access export
%auto_implicits off

compareTags : {e, l, l' : _} -> (t1 : Tag l e) -> (t2 : Tag l' e) -> Either (t1 = t2) Bool
compareTags  Z     Z    = Left Refl
compareTags  Z    (S _) = Right True
compareTags (S _)  Z    = Right False
compareTags (S x) (S y) with (compareTags x y)
  compareTags (S y) (S y) | Left Refl = Left Refl
  compareTags  _     _    | Right r = Right r

mutual
  gleqd : {e, Ix: _} -> (dR: TaggedDesc e Ix) -> (cstrsR: TaggedConstraints SOrd dR)
                     -> (d: Desc Ix) -> (cstrs: Constraints SOrd d)
                     -> {ix: Ix} -> (X, Y: Synthesize d (TaggedData dR) ix)
                     -> Bool
  gleqd _  _            (Ret _)       _         Refl       Refl       = True
  gleqd dR cstrsR (Arg _ kdesc) (_, ordr) (a1 ** r1) (a2 ** r2) with (choose (a1 <= a2))
    gleqd dR cstrsR (Arg _ kdesc) (_, ordr) (a1 ** r1) (a2 ** r2) | Left l with (choose (a2 <= a1))
      gleqd dR cstrsR (Arg _ kdesc) (_, ordr) (a1 ** r1) (a2 ** r2) | Left l | Left l'
       with (leqAntisymmetricReflective {x = a1} {y = a2} l l')
        gleqd dR cstrsR (Arg _ kdesc) (_, ordr) (a ** r1) (a ** r2) | Left _ | Left _ | Refl =
          assert_total $ gleqd dR cstrsR (kdesc a) (ordr a) r1 r2
      gleqd _  _            _             _         _          _          | Left _ | Right _ = True
    gleqd _ _ _ _ _ _ | Right _ = False
  gleqd dR cstrsR (Rec _ kdesc) cstrs (x1 ** r1) (x2 ** r2) with (assert_total $ gleq dR cstrsR x1 x2)
    gleqd _ _ _ _ _ _ | False = False
    gleqd dR cstrsR (Rec _ kdesc) cstrs (x1 ** r1) (x2 ** r2) | True with (assert_total $ gleq dR cstrsR x2 x1)
      gleqd _  _            _             _           _          _        | True | False = True
      gleqd dR cstrsR (Rec _ kdesc) cstrs (_ ** r1) (_ ** r2) | True | True = gleqd dR cstrsR kdesc cstrs r1 r2

  gleq : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (cstrs: TaggedConstraints SOrd d)
                    -> {ix: Ix} -> (X, Y : TaggedData d ix) -> Bool
  gleq d cstrs (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) with (compareTags t1 t2)
    gleq d cstrs (Con (l ** t ** r1)) (Con (l ** t ** r2)) | Left Refl = gleqd d cstrs (d l t) (cstrs l t) r1 r2
    gleq _ _           _                    _                    | Right r = r

compareTagsReflective : {e,l : _} -> (t : Tag l e) -> compareTags t t = Left Refl
compareTagsReflective  Z    = Refl
compareTagsReflective (S x) = rewrite compareTagsReflective x in Refl

compareTagsRightUnequal : {e, l, l', v : _} -> (t : Tag l e) -> (t' : Tag l' e)
                                            -> compareTags t t' = Right v -> Not (t = t')
compareTagsRightUnequal  Z     Z    Refl _    impossible
compareTagsRightUnequal  Z    (S _) _    Refl impossible
compareTagsRightUnequal (S _)  Z    _    Refl impossible
compareTagsRightUnequal (S x) (S x) prf  Refl = absurd $ trans (sym $ compareTagsReflective (S x)) prf

compareTagsRightFRightFVoid : {e, l, l2, v : _} -> (t : Tag l e) -> (t2 : Tag l2 e)
                                                -> compareTags t t2 = Right v -> compareTags t2 t = Right v
                                                -> Void
compareTagsRightFRightFVoid {v = False}  Z     Z    Refl _    impossible
compareTagsRightFRightFVoid {v = False}  Z    (S _) Refl _    impossible
compareTagsRightFRightFVoid {v = False} (S _)  Z    _    Refl impossible
compareTagsRightFRightFVoid {v = False} (S x) (S y) prf prf1 with (compareTags x y) proof xleqy
  compareTagsRightFRightFVoid {v = False} (S _) (S _) Refl _ | Left Refl impossible
  compareTagsRightFRightFVoid {v = False} (S x) (S y) prf prf1 | Right False with (compareTags y x) proof yleqx
    compareTagsRightFRightFVoid {v = False} (S _) (S _) _ Refl | Right False | Left Refl impossible
    compareTagsRightFRightFVoid {v = False} (S x) (S y) _ _    | Right False | Right False =
      compareTagsRightFRightFVoid {v = False} x y (sym xleqy) (sym yleqx)
    compareTagsRightFRightFVoid {v = False} (S _) (S _) _ Refl | Right False | Right True impossible
  compareTagsRightFRightFVoid {v = False} (S _) (S _) Refl _ | Right True impossible
compareTagsRightFRightFVoid {v = True}  Z     Z    Refl _    impossible
compareTagsRightFRightFVoid {v = True}  Z    (S _) _    Refl impossible
compareTagsRightFRightFVoid {v = True} (S _)  Z    Refl _    impossible
compareTagsRightFRightFVoid {v = True} (S x) (S y) prf  prf1 with (compareTags x y) proof xleqy
  compareTagsRightFRightFVoid {v = True} (S _) (S _) Refl _    | Left Refl impossible
  compareTagsRightFRightFVoid {v = True} (S _) (S _) Refl _    | Right False impossible
  compareTagsRightFRightFVoid {v = True} (S x) (S y) prf  prf1 | Right True with (compareTags y x) proof yleqx
    compareTagsRightFRightFVoid {v = True} (S _) (S _) _ Refl | Right True | Left Refl impossible
    compareTagsRightFRightFVoid {v = True} (S _) (S _) _ Refl | Right True | Right False impossible
    compareTagsRightFRightFVoid {v = True} (S x) (S y) _ _ | Right True | Right True =
      compareTagsRightFRightFVoid {v = True} x y (sym xleqy) (sym yleqx)

compareTagsTransitive : (t1,t2,t3: _) -> compareTags t1 t3 = Right True
                                      -> compareTags t3 t2 = Right True
                                      -> compareTags t1 t2 = Right True
compareTagsTransitive  Z     _     Z    Refl _    impossible
compareTagsTransitive  Z     Z    (S _) _    Refl impossible
compareTagsTransitive  Z    (S y) (S x) prf  prf1 with (compareTags x y) proof cxy
  compareTagsTransitive Z (S _) (S _) _   Refl | Left Refl impossible
  compareTagsTransitive Z (S _) (S _) prf prf1 | Right _ = Refl
compareTagsTransitive (S _)  Z     Z    _   Refl impossible
compareTagsTransitive (S _)  Z    (S _) _   Refl impossible
compareTagsTransitive (S x) (S y)  t3   prf prf1 with (compareTags x y) proof cxy
  compareTagsTransitive (S _) (S _) Z     Refl _    | Left Refl impossible
  compareTagsTransitive (S y) (S y) (S x) prf  prf1 | Left Refl with (compareTags y x) proof cyx
    compareTagsTransitive (S _) (S _) (S _) Refl _    | Left Refl | Left Refl impossible
    compareTagsTransitive (S _) (S _) (S _) Refl _    | Left Refl | Right False impossible
    compareTagsTransitive (S y) (S y) (S x) prf  prf1 | Left Refl | Right True with (compareTags x y) proof cxy'
      compareTagsTransitive (S _) (S _) (S _) _ Refl | Left Refl | Right True | Left Refl impossible
      compareTagsTransitive (S _) (S _) (S _) _ Refl | Left Refl | Right True | Right False impossible
      compareTagsTransitive (S y) (S y) (S x) _ _    | Left Refl | Right True | Right True =
        absurd $ trans cxy $ compareTagsTransitive y y x (sym cyx) (sym cxy')
  compareTagsTransitive (S _) (S _)  Z    Refl _    | Right False impossible
  compareTagsTransitive (S x) (S y) (S z) prf  prf1 | Right False with (compareTags x z) proof cxz
    compareTagsTransitive (S _) (S _) (S _) Refl _ | Right False | Left Refl impossible
    compareTagsTransitive (S _) (S _) (S _) Refl _ | Right False | Right False impossible
    compareTagsTransitive (S x) (S y) (S z) prf prf1 | Right False | Right True with (compareTags z y) proof czy
      compareTagsTransitive (S _) (S _) (S _) _ Refl | Right False | Right True | Left Refl impossible
      compareTagsTransitive (S _) (S _) (S _) _ Refl | Right False | Right True | Right False impossible
      compareTagsTransitive (S x) (S y) (S z) _ _    | Right False | Right True | Right True =
        absurd $ rightInjective $ trans cxy $ compareTagsTransitive x y z (sym cxz) (sym czy)
  compareTagsTransitive (S _) (S _) _     _   _    | Right True = Refl

mutual
  gleqdReflexive : {e, Ix: _} -> (dR: TaggedDesc e Ix) -> (cstrsR: TaggedConstraints SOrd dR)
                              -> (d: Desc Ix) -> (cstrs: Constraints SOrd d)
                              -> {ix: Ix} -> (X: Synthesize d (TaggedData dR) ix)
                              -> So (gleqd dR cstrsR d cstrs X X)
  gleqdReflexive _  _            (Ret _)       _ Refl = Oh
  gleqdReflexive dR cstrsR (Arg _ kdesc) (_, sordr) (arg ** rest) with (choose (arg <= arg))
    gleqdReflexive dR cstrsR (Arg _ kdesc) (_, sordr) (arg ** rest) | Left l with (choose (arg <= arg)) -- why do we need to do this again
      gleqdReflexive dR cstrsR (Arg _ kdesc) (_, sordr) (arg ** rest) | Left l | Left x with (leqAntisymmetricReflective {x = arg} {y = arg} l x)
        gleqdReflexive dR cstrsR (Arg _ kdesc) (_, sordr) (arg ** rest) | Left _ | Left _ | Refl =
          assert_total $ gleqdReflexive dR cstrsR (kdesc arg) (sordr arg) rest
      gleqdReflexive dR cstrsR (Arg _ kdesc) (_, sordr) (arg ** rest) | Left _ | Right _ = Oh -- This seems counter-intuitive but looks true-ish
    gleqdReflexive dR cstrsR (Arg _ kdesc) (_, sordr) (arg ** rest) | Right r = void (soNotSo (leqReflexive {x = arg}) r)
  gleqdReflexive dR cstrsR (Rec _ kdesc) cstrs (rec ** rest) =
    rewrite soToEq (assert_total $ gleqReflexive dR cstrsR rec) in
    rewrite soToEq (assert_total $ gleqReflexive dR cstrsR rec) in
    gleqdReflexive dR cstrsR kdesc cstrs rest

  gleqReflexive : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (cstrs: TaggedConstraints SOrd d)
                             -> {ix: Ix} -> (X: TaggedData d ix)
                             -> So (gleq d cstrs X X)
  gleqReflexive d cstrs (Con (l ** t ** r)) with (compareTags t t) proof cptag
    gleqReflexive d cstrs (Con (l ** t ** r)) | Left Refl = gleqdReflexive d cstrs (d l t) (cstrs l t) r
    gleqReflexive _ _           (Con (_ ** t ** _)) | Right _ = absurd (trans cptag (compareTagsReflective t))

mutual
  gleqdTotal : {e, Ix: _} -> (dR: TaggedDesc e Ix) -> (cstrsR: TaggedConstraints SOrd dR)
                          -> (d: Desc Ix) -> (cstrs: Constraints SOrd d)
                          -> {ix: Ix} -> (X, Y: Synthesize d (TaggedData dR) ix)
                          -> Either (So (gleqd dR cstrsR d cstrs X Y)) (So (gleqd dR cstrsR d cstrs Y X))
  gleqdTotal _ _ (Ret _) _ Refl Refl = Left Oh
  gleqdTotal dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) with (choose (a1 <= a2))
    gleqdTotal dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) | Left l with (choose (a2 <= a1))
      gleqdTotal dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) | Left l | Left x with (leqAntisymmetricReflective {x = a1} {y = a2} l x)
        gleqdTotal dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) | Left l | Left x | Refl with (assert_total $ gleqdTotal dR cstrsR (kdesc a) (sordr a) r1 r2)
          gleqdTotal _  _            _             _          _         _         | Left _ | Left _ | Refl | Left y = Left y
          gleqdTotal dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) | Left l | Left x | Refl | Right r with (choose (a <= a))
            gleqdTotal dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) | Left l | Left x | Refl | Right r | Left y with (leqAntisymmetricReflective {x = a} {y = a} x y)
              gleqdTotal dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) | Left _ | Left _ | Refl | Right _ | Left _ | Refl =
                assert_total $ gleqdTotal dR cstrsR (kdesc a) (sordr a) r1 r2
            gleqdTotal _  _            _             _          _         _         | Left _ | Left x | Refl | Right _ | Right y = void (soNotSo x y)
      gleqdTotal _  _            _               _          _         _         | Left _ | Right _ = Left Oh
    gleqdTotal dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) | Right r with (choose (a2 <= a1))
      gleqdTotal dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) | Right r | Left l with (choose (a1 <= a2))
        gleqdTotal dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) | Right r | Left l | Left x with (leqAntisymmetricReflective {x = a2} {y = a1} l x)
          gleqdTotal _ _ _ _ _ _ | Right r | Left l | Left _ | Refl = void (soNotSo l r)
        gleqdTotal _  _            _               _          _         _         | Right _ | Left _ | Right _ = Right Oh
      gleqdTotal dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) | Right r | Right x =
        case leqTotal {x = a1} {y = a2} of
          Left l => void (soNotSo l r)
          Right y => void (soNotSo y x)
  gleqdTotal dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) with (gleq dR cstrsR ra1 ra2) proof ra1leqra2
    gleqdTotal dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) | False with (gleq dR cstrsR ra2 ra1) proof ra2leqra1
      gleqdTotal dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) | False | False with (assert_total $ gleqTotal dR cstrsR ra1 ra2)
        gleqdTotal dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) | False | False | Left l with (trans ra1leqra2 (soToEq l))
          gleqdTotal _ _ (Rec _ _) _ (_ ** _) (_ ** _) | False | False | Left _ | Refl impossible
        gleqdTotal dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) | False | False | Right r with (trans ra2leqra1 (soToEq r))
          gleqdTotal _ _ (Rec _ _) _ (_ ** _) (_ ** _) | False | False | Right _ | Refl impossible
      gleqdTotal dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) | False | True with (gleqd dR cstrsR kdesc cstrs r2 r1) proof r2leqr1
        gleqdTotal _ _ _ _ _ _ | False | True | False = rewrite sym ra1leqra2 in Right Oh
        gleqdTotal _ _ _ _ _ _ | False | True | True = rewrite sym ra1leqra2 in Right Oh
    gleqdTotal dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) | True with (gleq dR cstrsR ra2 ra1) proof ra2leqra1
      gleqdTotal _  _            _             _           _           _           | True | False = Left Oh
      gleqdTotal dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) | True | True with (gleqd dR cstrsR kdesc cstrs r1 r2) proof r1leqr2
        gleqdTotal dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) | True | True | False with (gleqd dR cstrsR kdesc cstrs r2 r1) proof r2leqr1
          gleqdTotal dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) | True | True | False | False =
            case assert_total $ gleqdTotal dR cstrsR kdesc cstrs r1 r2 of
              Left l => absurd (trans r1leqr2 (soToEq l))
              Right r => absurd (trans r2leqr1 (soToEq r))
          gleqdTotal _  _            _             _           _           _           | True | True | False | True =
            rewrite sym ra1leqra2 in
            rewrite sym r2leqr1 in
            Right Oh
        gleqdTotal _  _            _             _           _           _           | True | True | True = Left Oh

  gleqTotal : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (cstrs: TaggedConstraints SOrd d)
                         -> {ix: Ix} -> (X, Y: TaggedData d ix)
                         -> Either (So (gleq d cstrs X Y)) (So (gleq d cstrs Y X))
  gleqTotal d cstrs (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) with (compareTags t1 t2) proof t1leqt2
    gleqTotal d cstrs (Con (l ** t ** r1))   (Con (l ** t ** r2))   | Left Refl =
      rewrite compareTagsReflective t in
      gleqdTotal d cstrs (d l t) (cstrs l t) r1 r2
    gleqTotal _ _           (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) | Right False with (compareTags t2 t1) proof t2leqt1
      gleqTotal _ _ (Con (l ** t ** _))  (Con (l ** t ** _))  | Right False | Left Refl =
        void (compareTagsRightUnequal t t (sym t1leqt2) Refl)
      gleqTotal _ _ (Con (_ ** t1 ** _)) (Con (_ ** t2 ** _)) | Right False | Right False =
        void (compareTagsRightFRightFVoid t1 t2 (sym t1leqt2) (sym t2leqt1))
      gleqTotal _ _ (Con _)              (Con _)              | Right False | Right True = Right Oh
    gleqTotal _ _           (Con _)                (Con _)                | Right True = Left Oh

mutual
  gleqdAntisymmetricReflexive : {e, Ix: _} -> (dR: TaggedDesc e Ix) -> (cstrsR: TaggedConstraints SOrd dR)
                                           -> (d : Desc Ix) -> (cstrs: Constraints SOrd d)
                                           -> {ix : Ix} -> (X, Y: Synthesize d (TaggedData dR) ix)
                                           -> So (gleqd dR cstrsR d cstrs X Y)
                                           -> So (gleqd dR cstrsR d cstrs Y X)
                                           -> X = Y
  gleqdAntisymmetricReflexive _ _ (Ret _) _ Refl Refl _ _ = Refl
  gleqdAntisymmetricReflexive dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) xleqy yleqx with (choose (a1 <= a2))
    gleqdAntisymmetricReflexive dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) xleqy yleqx | Left l with (choose (a2 <= a1))
      gleqdAntisymmetricReflexive dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) xleqy yleqx | Left l | Left x with (leqAntisymmetricReflective {x = a1} {y = a2} l x)
        gleqdAntisymmetricReflexive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) xleqy yleqx | Left l | Left x | Refl with (choose (gleqd dR cstrsR (kdesc a) (sordr a) r1 r2))
          gleqdAntisymmetricReflexive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) xleqy yleqx | Left l | Left x | Refl | Left y with (choose (a <= a))
            gleqdAntisymmetricReflexive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) xleqy yleqx | Left l | Left x | Refl | Left y | Left z with (leqAntisymmetricReflective {x = a} {y = a} x z)
              gleqdAntisymmetricReflexive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) xleqy yleqx | Left l | Left x | Refl | Left y | Left z | Refl =
                assert_total $ cong {f=\x=>(a**x)} $ gleqdAntisymmetricReflexive dR cstrsR (kdesc a) (sordr a) r1 r2 xleqy yleqx
            gleqdAntisymmetricReflexive _  _            _             _          _         _         _     _     | Left _ | Left x | Refl | Left _ | Right r = void (soNotSo x r)
          gleqdAntisymmetricReflexive _  _            _             _          _         _         xleqy _     | Left _ | Left _ | Refl | Right y = void (soNotSo xleqy y)
      gleqdAntisymmetricReflexive _  _            _             _          _          _          _     yleqx | Left _ | Right _ = absurd yleqx
    gleqdAntisymmetricReflexive _  _            _             _          _         _         xleqy _ | Right _ = absurd xleqy
  gleqdAntisymmetricReflexive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) xleqy yleqx with (gleq dR cstrsR ra1 ra2) proof ra1leqra2
    gleqdAntisymmetricReflexive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) xleqy yleqx | True with (gleq dR cstrsR ra2 ra1) proof ra2leqra1
      gleqdAntisymmetricReflexive _  _            _             _           _            _          _     yleqx | True | False = absurd yleqx
      gleqdAntisymmetricReflexive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) xleqy yleqx | True | True with (gleq dR cstrsR ra1 ra2) proof ra1leqra2'
        gleqdAntisymmetricReflexive _  _            _             _           _            _          _     _     | True | True | False = absurd ra1leqra2
        gleqdAntisymmetricReflexive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) xleqy yleqx | True | True | True with (assert_total $ gleqdAntisymmetricReflexive dR cstrsR kdesc cstrs r1 r2 xleqy yleqx)
          gleqdAntisymmetricReflexive dR cstrsR _ _ (ra1 ** r2) (ra2 ** r2) _ _ | True | True | True | Refl with (gleqAntisymmetricReflexive dR cstrsR ra1 ra2 (eqToSo $ sym ra1leqra2') (eqToSo $ sym ra2leqra1))
            gleqdAntisymmetricReflexive _ _ _ _ _ _ _ _ | True | True | True | Refl | Refl = Refl
    gleqdAntisymmetricReflexive _  _            _             _           _            _          xleqy _     | False = absurd xleqy

  gleqAntisymmetricReflexive : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (cstrs: TaggedConstraints SOrd d)
                                          -> {ix : Ix} -> (X, Y: TaggedData d ix)
                                          -> So (gleq d cstrs X Y) -> So (gleq d cstrs Y X)
                                          -> X = Y
  gleqAntisymmetricReflexive d cstrs (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) xleqy yleqx with (compareTags t1 t2) proof t1leqt2
    gleqAntisymmetricReflexive d cstrs (Con (l ** t ** r1)) (Con (l ** t ** r2)) xleqy yleqx | Left Refl with (compareTags t t) proof tleqt
      gleqAntisymmetricReflexive d cstrs (Con (l ** t ** r1)) (Con (l ** t ** r2)) xleqy yleqx | Left Refl | Left Refl with (assert_total $ gleqdAntisymmetricReflexive d cstrs (d l t) (cstrs l t) r1 r2 xleqy yleqx)
        gleqAntisymmetricReflexive _ _ _ _ _ _ | Left Refl | Left Refl | Refl = Refl
      gleqAntisymmetricReflexive _ _           (Con _)              (Con _)              _     _     | Left Refl | Right _ = absurd t1leqt2
    gleqAntisymmetricReflexive _ _           (Con _)                (Con _)                xleqy _     | Right False = absurd xleqy
    gleqAntisymmetricReflexive d cstrs (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) xleqy yleqx | Right True with (compareTags t2 t1) proof t2leqt1
      gleqAntisymmetricReflexive _ _ (Con _)              (Con _)              _ _     | Right True | Left Refl   = absurd $ trans t1leqt2 (sym t2leqt1)
      gleqAntisymmetricReflexive _ _ (Con _)              (Con _)              _ yleqx | Right True | Right False = absurd yleqx
      gleqAntisymmetricReflexive _ _ (Con (_ ** t1 ** _)) (Con (_ ** t2 ** _)) _ _     | Right True | Right True =
        void $ compareTagsRightFRightFVoid t1 t2 (sym t1leqt2) (sym t2leqt1)

mutual
  gleqdTransitive : {e, Ix: _} -> (dR: TaggedDesc e Ix) -> (cstrsR: TaggedConstraints SOrd dR)
                               -> (d: Desc Ix) -> (cstrs: Constraints SOrd d)
                               -> {ix : Ix} -> (x, y, z: Synthesize d (TaggedData dR) ix)
                               -> So (gleqd dR cstrsR d cstrs x z)
                               -> So (gleqd dR cstrsR d cstrs z y)
                               -> So (gleqd dR cstrsR d cstrs x y)
  gleqdTransitive _ _ (Ret _) _ Refl Refl Refl _ _ = Oh
  gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy with (choose (a1 <= a2))
    gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | Left l with (choose (a2 <= a1))
      gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | Left l | Left x with (leqAntisymmetricReflective {x = a1} {y = a2} l x)
        gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | Left l | Left x | Refl with (choose (a <= a3))
          gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | Left l | Left x | Refl | Left y with (choose (a3 <= a))
            gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | Left l | Left x | Refl | Left y | Left z with (choose (a <= a3))
              gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | Left l | Left x | Refl | Left y | Left z | Left w with (leqAntisymmetricReflective {x = a} {y = a3} w z)
                gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) (a ** r3) xleqz zleqy | Left l | Left x | Refl | Left y | Left z | Left w | Refl with (leqAntisymmetricReflective {x = a} {y = a} y z)
                  gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) (a ** r3) xleqz zleqy | Left l | Left x | Refl | Left y | Left z | Left w | Refl | Refl with (leqAntisymmetricReflective {x = a} {y = a} z w)
                    gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) (a ** r3) xleqz zleqy | Left l | Left x | Refl | Left y | Left z | Left w | Refl | Refl | Refl =
                      assert_total $ gleqdTransitive dR cstrsR (kdesc a) (sordr a) r1 r2 r3 xleqz zleqy
              gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | Left l | Left x | Refl | Left y | Left z | Right r = void (soNotSo y r)
            gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | Left l | Left x | Refl | Left y | Right r = absurd zleqy
          gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a ** r1) (a ** r2) (a3 ** r3) xleqz zleqy | Left l | Left x | Refl | Right r = absurd xleqz
      gleqdTransitive _ _ (Arg _ _) (_, _) (_ ** _) (_ ** _) (_ ** _) _ _ | Left _ | Right _ = Oh
    gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | Right r with (choose (a1 <= a3))
      gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | Right r | Left l with (choose (a3 <= a2))
        gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | Right r | Left l | Left x = void (soNotSo (leqTransitive {x = a1} {z = a3} {y = a2} l x) r)
        gleqdTransitive _  _            _             _          _          _          _          _     zleqy | Right _ | Left _ | Right _ = absurd zleqy
      gleqdTransitive dR cstrsR (Arg _ kdesc) (_, sordr) (a1 ** r1) (a2 ** r2) (a3 ** r3) xleqz zleqy | Right _ | Right _ = absurd xleqz
  gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy with (gleq dR cstrsR ra1 ra2) proof ra1leqra2
    gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False with (gleq dR cstrsR ra1 ra3) proof ra1leqra3
      gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | False = absurd xleqz
      gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True with (gleq dR cstrsR ra3 ra1) proof ra3leqra1
        gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | False with (gleq dR cstrsR ra3 ra2) proof ra3leqra2
          gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | False | False = absurd zleqy
          gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | False | True with (gleq dR cstrsR ra2 ra3) proof ra2leqra3
            gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | False | True | False =
              absurd $ trans ra1leqra2 $ soToEq $ gleqTransitive dR cstrsR ra1 ra2 ra3 (eqToSo $ sym ra1leqra3) (eqToSo $ sym ra3leqra2)
            gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | False | True | True =
              absurd $ trans ra1leqra2 $ soToEq $ gleqTransitive dR cstrsR ra1 ra2 ra3 (eqToSo $ sym ra1leqra3) (eqToSo $ sym ra3leqra2)
        gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | True with (gleq dR cstrsR ra3 ra2) proof ra3leqra2
          gleqdTransitive _  _            (Rec _ _)     _           (_ ** _)    (_ ** _)    (_ ** _)    _     zleqy | False | True | True | False = absurd zleqy
          gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | False | True | True | True =
            absurd $ trans ra1leqra2 $ soToEq $ gleqTransitive dR cstrsR ra1 ra2 ra3 (eqToSo $ sym ra1leqra3) (eqToSo $ sym ra3leqra2)
    gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True with (gleq dR cstrsR ra2 ra1) proof ra2leqra1
      gleqdTransitive _  _            (Rec _ _)     _           (_ ** _)    (_ ** _)    (_ ** _)    _     _     | True | False = Oh
      gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True with (gleq dR cstrsR ra1 ra3) proof ra1leqra3
        gleqdTransitive _  _            (Rec _ _)     _           (_ ** _)    (_ ** _)    (_ ** _)    xleqz _     | True | True | False = absurd xleqz
        gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True with (gleq dR cstrsR ra3 ra1) proof ra3leqra1
          gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | False with (gleq dR cstrsR ra3 ra2) proof ra3leqra2
            gleqdTransitive _  _            (Rec _ _)     _           (_ ** _)    (_ ** _)    (_ ** _)    _     zleqy | True | True | True | False | False = absurd zleqy
            gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | False | True with (gleq dR cstrsR ra2 ra3) proof ra2leqra3
              gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | False | True | False =
                absurd $ trans ra3leqra1 $ soToEq $ gleqTransitive dR cstrsR ra3 ra1 ra2 (eqToSo $ sym ra3leqra2) (eqToSo $ sym ra2leqra1)
              gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | False | True | True =
                absurd $ trans ra3leqra1 $ soToEq $ gleqTransitive dR cstrsR ra3 ra1 ra2 (eqToSo $ sym ra3leqra2) (eqToSo $ sym ra2leqra1)
          gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | True with (gleq dR cstrsR ra3 ra2) proof ra3leqra2
            gleqdTransitive _  _            (Rec _ _)     _           (_ ** _)    (_ ** _)    (_ ** _)    _     zleqy | True | True | True | True | False = absurd zleqy
            gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | True | True with (gleq dR cstrsR ra2 ra3) proof ra2leqra3
              gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) (ra3 ** r3) xleqz zleqy | True | True | True | True | True | False =
                absurd $ trans ra2leqra3 $ soToEq $ gleqTransitive dR cstrsR ra2 ra3 ra1 (eqToSo $ sym ra2leqra1) (eqToSo $ sym ra1leqra3)
              gleqdTransitive dR cstrsR (Rec _ kdesc) cstrs (_ ** r1)   (_ ** r2)   (_ ** r3)   xleqz zleqy | True | True | True | True | True | True =
                gleqdTransitive dR cstrsR kdesc cstrs r1 r2 r3 xleqz zleqy

  gleqTransitive : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (cstrs: TaggedConstraints SOrd d)
                              -> {ix : Ix} -> (x, y, z: TaggedData d ix)
                              -> So (gleq d cstrs x z) -> So (gleq d cstrs z y)
                              -> So (gleq d cstrs x y)
  gleqTransitive d cstrs (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) (Con (l3 ** t3 ** r3)) xleqz zleqy with (compareTags t1 t3) proof ct1t3
    gleqTransitive d cstrs (Con (l ** t ** r1)) (Con (l2 ** t2 ** r2)) (Con (l ** t ** r3)) xleqz zleqy | Left Refl with (compareTags t t2) proof ctt2
      gleqTransitive d cstrs (Con (l ** t ** r1)) (Con (l ** t ** r2))   (Con (l ** t ** r3)) xleqz zleqy | Left Refl | Left Refl =
        assert_total $ gleqdTransitive d cstrs (d l t) (cstrs l t) r1 r2 r3 xleqz zleqy
      gleqTransitive _ _           (Con (l ** t ** _))  (Con _)                (Con (l ** t ** _))  _     zleqy | Left Refl | Right _ = zleqy
    gleqTransitive _ _           (Con _)                (Con _)                (Con _)                xleqz _     | Right False = absurd xleqz
    gleqTransitive d cstrs (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) (Con (l3 ** t3 ** r3)) xleqz zleqy | Right True with (compareTags t3 t2) proof ct3t2
      gleqTransitive d cstrs (Con (l1 ** t1 ** r1)) (Con (l ** t ** r2)) (Con (l ** t ** r3)) xleqz zleqy | Right True | Left Refl with (compareTags t1 t) proof ct1t
        gleqTransitive _ _ (Con (l ** t ** _)) (Con (l ** t ** _)) (Con (l ** t ** _)) _ _ | Right True | Left Refl | Left Refl = absurd ct1t3
        gleqTransitive _ _ (Con _)             (Con (l ** t ** _)) (Con (l ** t ** _)) _ _ | Right True | Left Refl | Right False = absurd $ rightInjective ct1t3
        gleqTransitive _ _ (Con _)             (Con (l ** t ** _)) (Con (l ** t ** _)) _ _ | Right True | Left Refl | Right True = Oh
      gleqTransitive _ _           (Con _)                (Con _)                (Con _)                _     zleqy | Right True | Right False = absurd zleqy
      gleqTransitive d cstrs (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) (Con (l3 ** t3 ** r3)) xleqz zleqy | Right True | Right True with (compareTags t1 t2) proof ct1t2
        gleqTransitive _ _ (Con (l ** t ** _))  (Con (l ** t ** _))  (Con (l3 ** t3 ** _)) _ _ | Right True | Right True | Left Refl =
          void (compareTagsRightFRightFVoid t t3 (sym ct1t3) (sym ct3t2))
        gleqTransitive _ _ (Con (_ ** t1 ** _)) (Con (_ ** t2 ** _)) (Con (_ ** t3 ** _))  _ _ | Right True | Right True | Right False =
          absurd $ rightInjective $ trans ct1t2 (compareTagsTransitive t1 t2 t3 (sym ct1t3) (sym ct3t2))
        gleqTransitive _ _ (Con _)              (Con _)              (Con _)               _ _ | Right True | Right True | Right True = Oh