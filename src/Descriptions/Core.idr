module Descriptions.Core

import public Helper

%hide Data

%default total
%access public export
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

data PDesc : (n : Nat) -> (Ix : Type) -> Type where
  PRet  : {n,Ix: _} -> (ix: Ix)  -> PDesc n Ix
  PArg  : {n,Ix: _} -> (A: Type) -> (kdesc: (a: A) -> PDesc n Ix) -> PDesc n Ix
  PPar  : {n,Ix: _} -> (k : Fin n) -> (kdesc: PDesc n Ix) -> PDesc n Ix
  PMap  : {n,Ix: _} -> (f : Type -> Type) -> (k : Fin n) -> (kdesc: PDesc n Ix) -> PDesc n Ix
  PRec  : {n,Ix: _} -> (ix: Ix)  -> (kdesc: PDesc n Ix) -> PDesc n Ix

PUnfold : {n, Ix: _} -> PDesc (S n) Ix -> Type -> PDesc n Ix
PUnfold (PRet ix) = \B => PRet ix
PUnfold (PArg A kdesc) = \B => PArg A (\a : A => PUnfold (kdesc a) B)
PUnfold (PPar FZ kdesc) = \B => PArg B (\_ => PUnfold kdesc B)
PUnfold (PPar (FS k) kdesc) = \B => PPar k (PUnfold kdesc B)
PUnfold (PMap F FZ kdesc) = \B => PArg (F B) (\_ => PUnfold kdesc B)
PUnfold (PMap F (FS k) kdesc) = \B => PMap F k (PUnfold kdesc B)
PUnfold (PRec ix kdesc) = \B => PRec ix (PUnfold kdesc B)

PDescToDesc : {Ix : Type} -> PDesc Z Ix -> Desc Ix
PDescToDesc (PRet ix) = Ret ix
PDescToDesc (PArg A kdesc) = Arg A (\a => PDescToDesc (kdesc a))
PDescToDesc (PPar k kdesc) = absurd k
PDescToDesc (PMap f k kdesc) = absurd k
PDescToDesc (PRec ix kdesc) = Rec ix (PDescToDesc kdesc)

PSynthesize : {n, Ix: _} -> PDesc n Ix -> FunTy (replicate n Type) ((Ix -> Type) -> (Ix -> Type))
PSynthesize {n = Z} x = Synthesize (PDescToDesc x)
PSynthesize {n = (S k)} x = \a => PSynthesize (PUnfold x a)

PData : {n, Ix: _} -> PDesc n Ix -> FunTy (replicate n Type) (Ix -> Type)
PData {n = Z} x = Data (PDescToDesc x)
PData {n = (S k)} x = \a => PData (PUnfold x a)

TaggedData : {Ix: _} -> {e: CtorEnum} -> TaggedDesc e Ix -> (Ix -> Type)
TaggedData d = Data (Untag d)

Constraints : {Ix: _} -> (Interface: Type -> Type) -> (d: Desc Ix) -> Type
Constraints Interface (Ret ix) = Unit
Constraints Interface (Arg A kdesc) = (Interface A, (a: A) -> Constraints Interface (kdesc a))
Constraints Interface (Rec ix kdesc) = Constraints Interface kdesc

TaggedConstraints : {e, Ix: _} -> (Interface: Type -> Type) -> (td: TaggedDesc e Ix) -> Type
TaggedConstraints {e} Interface td = (l : CtorLabel) -> (t : Tag l e) -> Constraints Interface (td l t)

PConstraints1 : {Ix: _} -> (Interface : (Type -> Type) -> Type) -> (d: PDesc (S Z) Ix) -> Type
PConstraints1 Interface (PRet ix) = ()
PConstraints1 Interface (PArg A kdesc) = (a : A) -> PConstraints1 Interface (kdesc a)
PConstraints1 Interface (PPar k kdesc) = PConstraints1 Interface kdesc
PConstraints1 Interface (PMap f k kdesc) = (Interface f, PConstraints1 Interface kdesc)
PConstraints1 Interface (PRec ix kdesc) = PConstraints1 Interface kdesc
