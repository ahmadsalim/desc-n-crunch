module Descriptions

import Language.Reflection
import Language.Reflection.Errors
import Language.Reflection.Utils

import Pruviloj
import Pruviloj.Internals

import Control.Isomorphism
import Syntax.PreorderReasoning
import Data.Vect

%default total
%auto_implicits off

data Desc : (Ix: Type) -> Type where
  Ret : {Ix: _} -> (ix: Ix)  -> Desc Ix
  Arg : {Ix: _} -> (A: Type) -> (kdesc: (a: A) -> Desc Ix) -> Desc Ix
  Rec : {Ix: _} -> (ix: Ix)  -> (kdesc: Desc Ix) -> Desc Ix

%name Desc d, desc

CtorLabel : Type
CtorLabel = String

CtorEnum : Type
CtorEnum = List CtorLabel

data Tag : CtorLabel -> CtorEnum -> Type where
  Z : {l, e: _}    ->  Tag l (l :: e)
  S : {l, l', e: _} -> Tag l e -> Tag l (l' :: e)

implementation Uninhabited (Tag _ []) where
  uninhabited Z impossible
  uninhabited (S t') impossible

TaggedDesc : (e: CtorEnum) -> (Ix: Type) -> Type
TaggedDesc e Ix = (l: CtorLabel) -> Tag l e -> Desc Ix

Untag : {e, Ix: _} -> TaggedDesc e Ix -> Desc Ix
Untag {e} d = Arg CtorLabel (\l => Arg (Tag l e) (\t => d l t))

Synthesize : {Ix: _} -> Desc Ix -> (Ix -> Type) -> (Ix -> Type)
Synthesize (Ret ix)       X jx = ix ~=~ jx
Synthesize (Arg A kdesc)  X jx = (a: A ** Synthesize (kdesc a) X jx)
Synthesize (Rec ix kdesc) X jx = (x: X ix ** Synthesize kdesc X jx)

data Data : {Ix: Type} -> Desc Ix -> Ix -> Type where
  Con : {Ix: _} -> {d : Desc Ix} -> {ix : Ix} -> Synthesize d (Data d) ix -> Data d ix

TaggedData : {Ix: _} -> {e: CtorEnum} -> TaggedDesc e Ix -> (Ix -> Type)
TaggedData d = Data (Untag d)

Constraints : {Ix: _} -> (Interface: Type -> Type) -> (d: Desc Ix) -> Type
Constraints Interface (Ret ix) = Unit
Constraints Interface (Arg A kdesc) = (Interface A, (a: A) -> Constraints Interface (kdesc a))
Constraints Interface (Rec ix kdesc) = Constraints Interface kdesc

TaggedConstraints : {e, Ix: _} -> (Interface: Type -> Type) -> (td: TaggedDesc e Ix) -> Type
TaggedConstraints {e} Interface td = (l : CtorLabel) -> (t : Tag l e) -> Constraints Interface (td l t)


||| Apply a constructor, inferring as many arguments as possible, and then solve remaining holes with some tactic
applyCtor : TTName -> Nat -> Elab () -> Elab ()
applyCtor cn argCount tac =
  do holes <- apply (Var cn) (replicate argCount True)
     solve
     for_ holes (flip inHole tac)

||| If the goal is one of the families named, then use its
||| constructors in the order that they were defined. Otherwise, use
||| the argument tactic. Do this recursively.
covering
dfsearch : Nat -> List TTName -> Elab () -> Elab ()
dfsearch Z _ _ =
  fail [TextPart "Search failed because the depth limit was reached."]
dfsearch (S k) tns tac =
  do attack
     try $ repeatUntilFail intro'
     case headName !goalType of
       Nothing => tac
       Just n =>
         if not (n `elem` tns)
           then tac
           else do ctors <- constructors <$> lookupDatatypeExact n
                   choice (map (\(cn, args, _) =>
                                 applyCtor cn (length args) (dfsearch k tns tac))
                               ctors)
     solve -- the attack

covering
iddfsearch : Nat -> List TTName -> Elab () -> Elab ()
iddfsearch k tns tac = choice $ map (\i => dfsearch i tns tac) [0..k]

covering
resolveTCPlus : Elab ()
resolveTCPlus = iddfsearch 100 [`{Unit}, `{Pair}] (resolveTC `{resolveTCPlus})

paranthesize : String -> String
paranthesize str = if length (words str) <= 1 then str else "(" ++ str ++ ")"

mutual
  gshowd : {e, Ix: _} -> (dr: TaggedDesc e Ix) -> (constraintsr: TaggedConstraints Show dr)
    -> (d: Desc Ix) -> (constraints: Constraints Show d)
    -> {ix: Ix} -> (synth: Synthesize d (TaggedData dr) ix) -> String
  gshowd dr constraintsr (Ret ix) () Refl = ""
  gshowd dr constraintsr (Arg A kdesc) (showa, showkdesc) (arg ** rest) =
    " " ++ paranthesize (show @{showa} arg)
        ++ gshowd dr constraintsr (kdesc arg) (showkdesc arg) rest
  gshowd dr constraintsr (Rec ix kdesc) constraints (rec ** rest) =
    " " ++ paranthesize (gshow dr constraintsr rec)
        ++ gshowd dr constraintsr kdesc constraints rest


  gshow : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (constraints: TaggedConstraints Show d)
                    -> {ix : Ix} -> (X : TaggedData d ix) -> String
  gshow d constraints (Con (label ** (tag ** rest))) =
    let constraints' = constraints label tag
    in let showrest = assert_total $ gshowd d constraints (d label tag) constraints' rest
    in label ++ showrest

lemma_TagZnotS : {l,e:_} -> {t : Tag l e} -> Descriptions.Z = Descriptions.S t -> Void
lemma_TagZnotS Refl impossible

lemma_TagSInjective : {l,lr,e,er:_} -> {t : Tag l e} -> {t' : Tag lr er}
                     -> Descriptions.S t = Descriptions.S t' -> t = t'
lemma_TagSInjective Refl = Refl

using (l,e:_)
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


---- Examples
VecCtors : CtorEnum
VecCtors = [ "Nil" , "Cons" ]

NilTag : Tag "Nil" VecCtors
NilTag = %runElab search

ConsTag : Tag "Cons" VecCtors
ConsTag = %runElab search

VecDesc : (A : Type) -> TaggedDesc VecCtors Nat
VecDesc A _ Z = Ret Z
VecDesc A _ (S Z) = Arg Nat (\n => Arg A (\a => Rec n (Ret (S n))))
VecDesc A _ (S (S k)) = absurd k

Vec : (A : Type) -> Nat -> Type
Vec A n = TaggedData (VecDesc A) n

Nil : {A: Type} -> Vec A Z
Nil = Con ("Nil" ** (Z ** Refl))

Cons : {A: Type} -> {n: Nat} -> A -> Vec A n -> Vec A (S n)
Cons {n} x xs = Con ("Cons" ** (S Z ** (n ** (x ** (xs ** Refl)))))

exampleVec : Vec String 2
exampleVec = Cons "Hello" (Cons "World" Nil)

exampleVec' : Vec String 2
exampleVec' = Cons "World" (Cons "Hello" Nil)

VecShowConstraints : {A : Type} -> (Show A) => TaggedConstraints Show (VecDesc A)
VecShowConstraints = \l, t =>
  case t of
    Z => %runElab resolveTCPlus
    S Z => %runElab resolveTCPlus
    S (S Z) impossible

exampleVecShown : gshow (VecDesc String) (VecShowConstraints {A = String}) exampleVec = """Cons 1 "Hello" (Cons 0 "World" Nil)"""
exampleVecShown = Refl

VecDecEqConstraints : {A : Type} -> (DecEq A) => TaggedConstraints DecEq (VecDesc A)
VecDecEqConstraints = \l, t =>
  case t of
    Z => %runElab resolveTCPlus
    S Z => %runElab resolveTCPlus
    S (S Z) impossible

exampleVecDecEqSelf : gdecEq (VecDesc String) (VecDecEqConstraints {A = String}) exampleVec exampleVec = Yes Refl
exampleVecDecEqSelf = Refl

exampleVecDecEqNil : (contra ** gdecEq (VecDesc String) (VecDecEqConstraints {A = String}) exampleVec exampleVec' = No contra)
exampleVecDecEqNil = (_ ** Refl)

toVecDesc : {A, n: _} -> Vect n A -> Vec A n
toVecDesc [] = []
toVecDesc (x :: xs) = Cons x (toVecDesc xs)
fromVecDesc : {A, n: _} -> Vec A n -> Vect n A
fromVecDesc (Con ("Nil" ** (Z ** Refl))) = []
fromVecDesc (Con ("Cons" ** (S Z ** (n ** (x ** (xs ** Refl)))))) = x :: fromVecDesc xs
fromVecDesc (Con (_ ** (S (S Z) ** res))) impossible
toFromVecDesc : {A, n: _} -> (xs : Vec A n) -> toVecDesc (fromVecDesc xs) = xs
toFromVecDesc (Con ("Nil" ** (Z ** Refl))) = Refl
toFromVecDesc (Con ("Cons" ** (S Z ** (n ** (x ** (xs ** Refl)))))) with (toFromVecDesc xs)
  toFromVecDesc (Con ("Cons" ** (S Z ** (n ** (x ** (xs ** Refl)))))) | ih = rewrite ih in Refl
toFromVecDesc (Con (_ ** (S (S Z) ** res))) impossible
fromToVecDesc : {A, n: _} -> (xs : Vect n A) -> fromVecDesc (toVecDesc xs) = xs
fromToVecDesc [] = Refl
fromToVecDesc (x :: xs) with (fromToVecDesc xs)
  fromToVecDesc (x :: xs) | ih = rewrite ih in Refl

vecIso : {A, n: _} -> Iso (Vect n A) (Vec A n)
vecIso = MkIso toVecDesc fromVecDesc toFromVecDesc fromToVecDesc

isoTo : {A, B : Type} -> Iso A B -> A -> B
isoTo (MkIso to from toFrom fromTo) = to

decEqIso : {A, B: Type} -> {a1, a2: A} ->
           (iso : Iso A B) -> Dec (a1 = a2) ->
             Dec (isoTo iso a1 = isoTo iso a2)
decEqIso (MkIso to from toFrom fromTo) (Yes prf) = Yes (cong prf)
decEqIso {a1} {a2} (MkIso to from toFrom fromTo) (No contra) =
  No (\prf =>
    let prf': (from (to a1) = from (to a2)) = cong prf
    in let prf'' = replace {P = \a => a = from (to a2)} (fromTo a1) prf'
    in let prf''' = replace {P = \a => a1 = a} (fromTo a2) prf''
    in contra prf''')
