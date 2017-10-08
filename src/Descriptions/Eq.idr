module Descriptions.Eq

import Interfaces
import Descriptions.Core
import Descriptions.DecEq
import Helper

%default total
%access export
%auto_implicits off

mutual
  geqd : {e, Ix: _} -> (dr: TaggedDesc e Ix) -> (constraintsr: TaggedConstraints SEq dr)
                    -> (d: Desc Ix) -> (constraints: Constraints SEq d)
                    -> {ix: Ix} -> (X, Y: Synthesize d (TaggedData dr) ix) -> Bool
  geqd _ _ (Ret _) _ Refl Refl = True
  geqd dr constraintsr (Arg A kdesc) (eqa, eqr) (a1 ** r1) (a2 ** r2) with (choose ((==) a1 a2))
    geqd dr constraintsr (Arg A kdesc) (eqa, eqr) (a1 ** r1) (a2 ** r2) | Left l with (eqReflective @{eqa} l)
      geqd dr constraintsr (Arg _ kdesc) (_, eqr) (a ** r1) (a ** r2) | Left _ | Refl = assert_total $ geqd dr constraintsr (kdesc a) (eqr a) r1 r2
    geqd _  _            _             _          _          _          | Right _ = False
  geqd dr constraintsr (Rec _ kdesc) constraints (x1 ** r1) (x2 ** r2) = assert_total $ geq dr constraintsr x1 x2 && geqd dr constraintsr kdesc constraints r1 r2

  geq : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints SEq d) -> {ix: Ix} -> (X : TaggedData d ix) -> (Y : TaggedData d ix) -> Bool
  geq d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) with (decEq l1 l2)
    geq d constraints (Con (l ** t1 ** r1)) (Con (l ** t2 ** r2)) | Yes Refl with (decEq t1 t2)
      geq d constraints (Con (l ** t ** r1)) (Con (l ** t ** r2)) | Yes Refl | Yes Refl = geqd d constraints (d l t) (constraints l t) r1 r2
      geq _ _           (Con (l ** _ ** _))  (Con (l ** _ ** _))  | Yes Refl | No _     = False
    geq _ _           _                     _                     | No _ = False

mutual
  geqdReflective : {e, Ix: _} -> (dr: TaggedDesc e Ix) -> (constraintsr: TaggedConstraints SEq dr)
                              -> (d: Desc Ix) -> (constraints: Constraints SEq d)
                              -> {ix: Ix} -> (X, Y: Synthesize d (TaggedData dr) ix)
                              -> So (geqd dr constraintsr d constraints X Y) -> X = Y
  geqdReflective _ _ (Ret _) _ Refl Refl _ = Refl
  geqdReflective dr constraintsr (Arg _ kdesc) (seqa, seqr) (a1 ** r1) (a2 ** r2) soeq with (choose (a1 == a2))
    geqdReflective dr constraintsr (Arg _ kdesc) (seqa, seqr) (a1 ** r1) (a2 ** r2) soeq | Left l with (eqReflective @{seqa} l)
      geqdReflective dr constraintsr (Arg _ kdesc) (_, seqr) (a ** r1) (a ** r2) soeq | Left _ | Refl with (assert_total $ geqdReflective dr constraintsr (kdesc a) (seqr a) r1 r2 soeq)
        geqdReflective _ _ _ _ _ _ _ | Left _ | Refl | Refl = Refl
    geqdReflective _ _ (Arg _ _) (_, _) (_ ** _) (_ ** _) Oh | Right _ impossible
  geqdReflective dr constraintsr (Rec _ kdesc) constraints (ra1 ** r1) (ra2 ** r2) soeq with (assert_total $ geqReflective dr constraintsr ra1 ra2 (fst $ soAndSo soeq))
    geqdReflective dr constraintsr (Rec _ kdesc) constraints (ra ** r1) (ra ** r2) soeq | Refl with (assert_total $ geqdReflective dr constraintsr kdesc constraints r1 r2 (snd $ soAndSo soeq))
      geqdReflective _ _ _ _ _ _ _ | Refl | Refl = Refl

  geqReflective :  {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints SEq d)
                              -> {ix: Ix} -> (X, Y: TaggedData d ix) -> So (geq d constraints X Y)
                              -> X = Y
  geqReflective d constraints (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) soeq with (decEq l1 l2)
    geqReflective d constraints (Con (l ** t1 ** r1)) (Con (l ** t2 ** r2)) soeq | Yes Refl with (decEq t1 t2)
      geqReflective d constraints (Con (l ** t ** r1)) (Con (l ** t ** r2)) soeq | Yes Refl | Yes Refl =
        cong {f = \x => Con (l ** t ** x)} $ geqdReflective d constraints (d l t) (constraints l t) r1 r2 soeq
      geqReflective _ _ _ _ Oh | Yes Refl | No _ impossible
    geqReflective _ _           (Con (_ ** _ ** _))   (Con (_ ** _ ** _))   Oh   | No _ impossible

mutual
  geqdReflexive : {e, Ix: _} -> (dr: TaggedDesc e Ix) -> (constraintsr: TaggedConstraints SEq dr)
                             -> (d: Desc Ix) -> (constraints: Constraints SEq d)
                             -> {ix: Ix} -> (X: Synthesize d (TaggedData dr) ix)
                             -> So (geqd dr constraintsr d constraints X X)
  geqdReflexive _ _ (Ret _) _ Refl = Oh
  geqdReflexive dr constraintsr (Arg _ kdesc) (seqa, seqr) (arg ** rest)  with (choose (arg == arg))
    geqdReflexive dr constraintsr (Arg _ kdesc) (seqa, seqr) (arg ** rest) | Left l with (eqReflective @{seqa} l)
      geqdReflexive dr constraintsr (Arg _ kdesc) (_, seqr) (arg ** rest) | Left _ | Refl =
        assert_total $ geqdReflexive dr constraintsr (kdesc arg) (seqr arg) rest
    geqdReflexive _  _            _             _            (arg ** _)    | Right r = void (soNotSo (eqReflexive {x = arg}) r)
  geqdReflexive dr constraintsr (Rec _ kdesc) constraints (rec ** rest) with (assert_total $ geqReflexive dr constraintsr rec)
    geqdReflexive dr constraintsr (Rec _ kdesc) constraints (_ ** rest) | recrefl =
      rewrite soToEq recrefl in geqdReflexive dr constraintsr kdesc constraints rest

  geqReflexive : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints SEq d)
                            -> {ix : Ix} -> (X : TaggedData d ix) -> So (geq d constraints X X)
  geqReflexive d constraints (Con (l ** t ** r)) =
    rewrite decEqSelfIsYes {x=l} in
    rewrite decEqSelfIsYes {x=t} in
    geqdReflexive d constraints (d l t) (constraints l t) r

geqSymmetric : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints SEq d)
                          -> {ix: Ix} -> (X, Y: TaggedData d ix) -> So (geq d constraints Y X)
                          -> So (geq d constraints X Y)
geqSymmetric d constraints X Y soeq with (geqReflective d constraints Y X soeq)
  geqSymmetric d constraints X X _ | Refl = geqReflexive d constraints X

geqTransitive : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints SEq d)
                           -> {ix: Ix} -> (X, Y, Z: TaggedData d ix)
                           -> So (geq d constraints X Z) -> So (geq d constraints Z Y)
                           -> So (geq d constraints X Y)
geqTransitive d constraints x y z soeq1 soeq2 with (geqReflective d constraints x z soeq1)
  geqTransitive d constraints x y x soeq1 soeq2 | Refl with (geqReflective d constraints x y soeq2)
    geqTransitive d constraints x x x _ _ | Refl | Refl = geqReflexive d constraints x
