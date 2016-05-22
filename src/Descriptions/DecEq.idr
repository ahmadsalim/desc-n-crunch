module Descriptions.DecEq

import Descriptions.Core as Core

%default total
%access export
%auto_implicits off

lemma_TagZnotS : {l,e:_} -> {t : Tag l e} -> Core.Z = Core.S t -> Void
lemma_TagZnotS Refl impossible

lemma_TagSInjective : {l,lr,e,er:_} -> {t : Tag l e} -> {t' : Tag lr er}
                     -> Core.S t = Core.S t' -> t = t'
lemma_TagSInjective Refl = Refl

using (l: CtorLabel, e: CtorEnum)
  implementation DecEq (Tag l e) where
    decEq Z Z = Yes Refl
    decEq Z (S _) = No lemma_TagZnotS
    decEq (S _) Z = No (negEqSym lemma_TagZnotS)
    decEq (S t1) (S t2) with (decEq t1 t2)
      decEq (S t1) (S t1) | (Yes Refl) = Yes Refl
      decEq (S t1) (S t2) | (No contra) = No (contra . lemma_TagSInjective)

lemma_DataConInjective : {x,y: _} -> Con x = Con y -> x = y
lemma_DataConInjective Refl = Refl

lemma_DPairFstInjective : {x,y,xs,ys: _} -> (x ** xs) = (y ** ys) -> x = y
lemma_DPairFstInjective Refl = Refl

lemma_DPairSndInjective : {x,y,xs,ys: _} -> (x ** xs) = (y ** ys) -> xs = ys
lemma_DPairSndInjective Refl = Refl

mutual
  gdecEqd : {e, Ix: _} -> (dr: TaggedDesc e Ix) -> (constraintsr: TaggedConstraints DecEq dr)
    -> (d: Desc Ix) -> (constraints: Constraints DecEq d)
    -> {ix: Ix} -> (synthX, synthY: Synthesize d (TaggedData dr) ix) -> Dec (synthX = synthY)
  gdecEqd dr constraintsr (Ret ix) () Refl Refl = Yes Refl
  gdecEqd dr constraintsr (Arg A kdesc) (decEqa, decEqkdesc) (arg1 ** rest1) (arg2 ** rest2) with (decEq @{decEqa} arg1 arg2)
    gdecEqd dr constraintsr (Arg A kdesc) (decEqa, decEqkdesc) (arg ** rest1) (arg ** rest2) | (Yes Refl)
     with (assert_total $ gdecEqd dr constraintsr (kdesc arg) (decEqkdesc arg) rest1 rest2)
      gdecEqd dr constraintsr (Arg A kdesc) (decEqa, decEqkdesc) (arg ** rest) (arg ** rest) | (Yes Refl) | (Yes Refl) = Yes Refl
      gdecEqd dr constraintsr (Arg A kdesc) (decEqa, decEqkdesc) (arg ** rest1) (arg ** rest2) | (Yes Refl) | (No contra) = No (contra . lemma_DPairSndInjective)
    gdecEqd dr constraintsr (Arg A kdesc) (decEqa, decEqkdesc) (arg1 ** rest1) (arg2 ** rest2) | (No contra) = No (contra . lemma_DPairFstInjective)
  gdecEqd dr constraintsr (Rec ix kdesc) decEqkdesc (rec1 ** rest1) (rec2 ** rest2) with (assert_total $ gdecEq dr constraintsr rec1 rec2)
    gdecEqd dr constraintsr (Rec ix kdesc) decEqkdesc (rec ** rest1) (rec ** rest2) | (Yes Refl)
     with (assert_total $ gdecEqd dr constraintsr kdesc decEqkdesc rest1 rest2)
      gdecEqd dr constraintsr (Rec ix kdesc) decEqkdesc (rec ** rest) (rec ** rest) | (Yes Refl) | (Yes Refl)  = Yes Refl
      gdecEqd dr constraintsr (Rec ix kdesc) decEqkdesc (rec ** rest1) (rec ** rest2) | (Yes Refl) | (No contra) = No (contra . lemma_DPairSndInjective)
    gdecEqd dr constraintsr (Rec ix kdesc) decEqkdesc (rec1 ** rest1) (rec2 ** rest2) | (No contra) = No (contra . lemma_DPairFstInjective)

  gdecEq : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints DecEq d)
              -> {ix : Ix} -> (X, Y : TaggedData d ix) -> Dec (X = Y)
  gdecEq d constraints (Con dtx) (Con dty) with (gdecEqd d constraints (Untag d) (%instance, \l => (%instance, \t => constraints l t)) dtx dty)
    gdecEq d constraints (Con dt) (Con dt) | (Yes Refl) = Yes Refl
    gdecEq d constraints (Con dtx) (Con dty) | (No contra) = No (contra . lemma_DataConInjective)
