module Descriptions.Eq

import Interfaces
import Descriptions.Core
import Descriptions.DecEq

%default total
%access export
%auto_implicits off

mutual
  geqd : {e, Ix: _} -> (dr: TaggedDesc e Ix) -> (constraintsr: TaggedConstraints SEq dr) -> (d: Desc Ix) -> (constraints: Constraints SEq d) -> {ix: Ix} -> (X: Synthesize d (TaggedData dr) ix) -> (Y: Synthesize d (TaggedData dr) ix) -> Bool
  geqd dr constraintsr (Ret ix) constraints Refl Refl = True
  geqd dr constraintsr (Arg A kdesc) (eqa, eqr) (a1 ** r1) (a2 ** r2) with (choose ((==) a1 a2))
    geqd dr constraintsr (Arg A kdesc) (eqa, eqr) (a1 ** r1) (a2 ** r2) | (Left l) with (eqReflective @{eqa} l)
      geqd dr constraintsr (Arg A kdesc) (eqa, eqr) (a ** r1) (a ** r2) | (Left l) | Refl = assert_total $ geqd dr constraintsr (kdesc a) (eqr a) r1 r2
    geqd dr constraintsr (Arg A kdesc) (eqa, eqr) (a1 ** r1) (a2 ** r2) | (Right r) = False

  geqd dr constraintsr (Rec ix kdesc) constraints (x1 ** r1) (x2 ** r2) = assert_total $ geq dr constraintsr x1 x2 && geqd dr constraintsr kdesc constraints r1 r2

  geq : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints SEq d) -> {ix: Ix} -> (X : TaggedData d ix) -> (Y : TaggedData d ix) -> Bool
  geq d constraints (Con (l1 ** (t1 ** r1))) (Con (l2 ** (t2 ** r2))) with (decEq l1 l2)
    geq d constraints (Con (l ** (t1 ** r1))) (Con (l ** (t2 ** r2))) | (Yes Refl) with (decEq t1 t2)
      geq d constraints (Con (l ** (t ** r1))) (Con (l ** (t ** r2))) | (Yes Refl) | (Yes Refl) = geqd d constraints (d l t) (constraints l t) r1 r2
      geq d constraints (Con (l ** (t1 ** r1))) (Con (l ** (t2 ** r2))) | (Yes Refl) | (No contra) = False
    geq d constraints (Con (l1 ** (t1 ** r1))) (Con (l2 ** (t2 ** r2))) | (No contra) = False

