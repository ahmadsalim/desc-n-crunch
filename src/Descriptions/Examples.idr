module Descriptions.Examples

import Descriptions.Core
import Descriptions.Show
import Descriptions.DecEq
import Control.Isomorphism

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

{-
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

  -}
