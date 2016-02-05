module Descriptions
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

VecCtors : CtorEnum
VecCtors = [ "Nil" , "Cons" ]

NilTag : Tag "Nil" VecCtors
NilTag = %runElab search

ConsTag : Tag "Cons" VecCtors
ConsTag = %runElab search

VecDesc : (A : Type) -> TaggedDesc VecCtors Nat
VecDesc A "Nil" Z = Ret Z
VecDesc A "Cons" (S Z) = Arg Nat (\n => Arg A (\a => Rec n (Ret (S n))))

Vec : (A : Type) -> Nat -> Type
Vec A n = TaggedData (VecDesc A) n

Nil : {A: Type} -> Vec A Z
Nil = Con ("Nil" ** (Z ** Refl))

Cons : {A: Type} -> {n: Nat} -> A -> Vec A n -> Vec A (S n)
Cons {n} x xs = Con ("Cons" ** (S Z ** (n ** (x ** (xs ** Refl)))))

exampleVec : Vec String 2
exampleVec = Cons "Hello" (Cons "World" Nil)
