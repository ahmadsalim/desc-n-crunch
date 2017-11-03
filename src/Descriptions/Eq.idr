module Descriptions.Eq

import Interfaces
import Descriptions.Core
import Descriptions.DecEq
import Helper

%default total
%access export
%auto_implicits off

mutual
  geqd : {e, Ix: _} -> (dR: TaggedDesc e Ix) -> (cstrsR: TaggedConstraints SEq dR)
                    -> (d: Desc Ix) -> (cstrs: Constraints SEq d)
                    -> {ix: Ix} -> (X, Y: Synthesize d (TaggedData dR) ix) -> Bool
  geqd _ _ (Ret _) _ Refl Refl = True
  geqd dR cstrsR (Arg A kdesc) (eqa, eqr) (a1 ** r1) (a2 ** r2) with (choose ((==) a1 a2))
    geqd dR cstrsR (Arg A kdesc) (eqa, eqr) (a1 ** r1) (a2 ** r2) | Left l with (eqReflective @{eqa} l)
      geqd dR cstrsR (Arg _ kdesc) (_, eqr) (a ** r1) (a ** r2) | Left _ | Refl = assert_total $ geqd dR cstrsR (kdesc a) (eqr a) r1 r2
    geqd _  _            _             _          _          _          | Right _ = False
  geqd dR cstrsR (Rec _ kdesc) cstrs (x1 ** r1) (x2 ** r2) = assert_total $ geq dR cstrsR x1 x2 && geqd dR cstrsR kdesc cstrs r1 r2

  geq : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (cstrs: TaggedConstraints SEq d) -> {ix: Ix} -> (X : TaggedData d ix) -> (Y : TaggedData d ix) -> Bool
  geq d cstrs (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) with (decEq l1 l2)
    geq d cstrs (Con (l ** t1 ** r1)) (Con (l ** t2 ** r2)) | Yes Refl with (decEq t1 t2)
      geq d cstrs (Con (l ** t ** r1)) (Con (l ** t ** r2)) | Yes Refl | Yes Refl = geqd d cstrs (d l t) (cstrs l t) r1 r2
      geq _ _           (Con (l ** _ ** _))  (Con (l ** _ ** _))  | Yes Refl | No _     = False
    geq _ _           _                     _                     | No _ = False

mutual
  geqdReflective : {e, Ix: _} -> (dR: TaggedDesc e Ix) -> (cstrsR: TaggedConstraints SEq dR)
                              -> (d: Desc Ix) -> (cstrs: Constraints SEq d)
                              -> {ix: Ix} -> (X, Y: Synthesize d (TaggedData dR) ix)
                              -> So (geqd dR cstrsR d cstrs X Y) -> X = Y
  geqdReflective _ _ (Ret _) _ Refl Refl _ = Refl
  geqdReflective dR cstrsR (Arg _ kdesc) (seqa, seqr) (a1 ** r1) (a2 ** r2) soeq with (choose (a1 == a2))
    geqdReflective dR cstrsR (Arg _ kdesc) (seqa, seqr) (a1 ** r1) (a2 ** r2) soeq | Left l with (eqReflective @{seqa} l)
      geqdReflective dR cstrsR (Arg _ kdesc) (_, seqr) (a ** r1) (a ** r2) soeq | Left _ | Refl with (assert_total $ geqdReflective dR cstrsR (kdesc a) (seqr a) r1 r2 soeq)
        geqdReflective _ _ _ _ _ _ _ | Left _ | Refl | Refl = Refl
    geqdReflective _ _ (Arg _ _) (_, _) (_ ** _) (_ ** _) Oh | Right _ impossible
  geqdReflective dR cstrsR (Rec _ kdesc) cstrs (ra1 ** r1) (ra2 ** r2) soeq with (assert_total $ geqReflective dR cstrsR ra1 ra2 (fst $ soAndSo soeq))
    geqdReflective dR cstrsR (Rec _ kdesc) cstrs (ra ** r1) (ra ** r2) soeq | Refl with (assert_total $ geqdReflective dR cstrsR kdesc cstrs r1 r2 (snd $ soAndSo soeq))
      geqdReflective _ _ _ _ _ _ _ | Refl | Refl = Refl

  geqReflective :  {e, Ix: _} -> (d: TaggedDesc e Ix) -> (cstrs: TaggedConstraints SEq d)
                              -> {ix: Ix} -> (X, Y: TaggedData d ix) -> So (geq d cstrs X Y)
                              -> X = Y
  geqReflective d cstrs (Con (l1 ** t1 ** r1)) (Con (l2 ** t2 ** r2)) soeq with (decEq l1 l2)
    geqReflective d cstrs (Con (l ** t1 ** r1)) (Con (l ** t2 ** r2)) soeq | Yes Refl with (decEq t1 t2)
      geqReflective d cstrs (Con (l ** t ** r1)) (Con (l ** t ** r2)) soeq | Yes Refl | Yes Refl =
        cong {f = \x => Con (l ** t ** x)} $ geqdReflective d cstrs (d l t) (cstrs l t) r1 r2 soeq
      geqReflective _ _ _ _ Oh | Yes Refl | No _ impossible
    geqReflective _ _           (Con (_ ** _ ** _))   (Con (_ ** _ ** _))   Oh   | No _ impossible

mutual
  geqdReflexive : {e, Ix: _} -> (dR: TaggedDesc e Ix) -> (cstrsR: TaggedConstraints SEq dR)
                             -> (d: Desc Ix) -> (cstrs: Constraints SEq d)
                             -> {ix: Ix} -> (X: Synthesize d (TaggedData dR) ix)
                             -> So (geqd dR cstrsR d cstrs X X)
  geqdReflexive _ _ (Ret _) _ Refl = Oh
  geqdReflexive dR cstrsR (Arg _ kdesc) (seqa, seqr) (arg ** rest)  with (choose (arg == arg))
    geqdReflexive dR cstrsR (Arg _ kdesc) (seqa, seqr) (arg ** rest) | Left l with (eqReflective @{seqa} l)
      geqdReflexive dR cstrsR (Arg _ kdesc) (_, seqr) (arg ** rest) | Left _ | Refl =
        assert_total $ geqdReflexive dR cstrsR (kdesc arg) (seqr arg) rest
    geqdReflexive _  _            _             _            (arg ** _)    | Right r = void (soNotSo (eqReflexive {x = arg}) r)
  geqdReflexive dR cstrsR (Rec _ kdesc) cstrs (rec ** rest) with (assert_total $ geqReflexive dR cstrsR rec)
    geqdReflexive dR cstrsR (Rec _ kdesc) cstrs (_ ** rest) | recrefl =
      rewrite soToEq recrefl in geqdReflexive dR cstrsR kdesc cstrs rest

  geqReflexive : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (cstrs: TaggedConstraints SEq d)
                            -> {ix : Ix} -> (X : TaggedData d ix) -> So (geq d cstrs X X)
  geqReflexive d cstrs (Con (l ** t ** r)) =
    rewrite decEqSelfIsYes {x=l} in
    rewrite decEqSelfIsYes {x=t} in
    geqdReflexive d cstrs (d l t) (cstrs l t) r

geqSymmetric : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (cstrs: TaggedConstraints SEq d)
                          -> {ix: Ix} -> (X, Y: TaggedData d ix) -> So (geq d cstrs Y X)
                          -> So (geq d cstrs X Y)
geqSymmetric d cstrs X Y soeq with (geqReflective d cstrs Y X soeq)
  geqSymmetric d cstrs X X _ | Refl = geqReflexive d cstrs X

geqTransitive : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (cstrs: TaggedConstraints SEq d)
                           -> {ix: Ix} -> (X, Y, Z: TaggedData d ix)
                           -> So (geq d cstrs X Z) -> So (geq d cstrs Z Y)
                           -> So (geq d cstrs X Y)
geqTransitive d cstrs x y z soeq1 soeq2 with (geqReflective d cstrs x z soeq1)
  geqTransitive d cstrs x y x soeq1 soeq2 | Refl with (geqReflective d cstrs x y soeq2)
    geqTransitive d cstrs x x x _ _ | Refl | Refl = geqReflexive d cstrs x
