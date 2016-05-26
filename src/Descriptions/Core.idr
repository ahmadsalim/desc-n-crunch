||| The main implementation of described types.
|||
||| Note that the examples in the documentation sometimes rely on
||| implicit arguments, so make sure to use the "show implicits"
||| command when reading the documentation.
module Descriptions.Core

import public Helper

%hide Data

%default total
%access public export
%auto_implicits off

||| A description of an indexed family of types.
|||
||| @ Ix the type over which the family is indexed
data Desc : (Ix: Type) -> Type where

  ||| The final constructor description, instantiating the family at a
  ||| particular index.
  Ret : {Ix: _} -> (ix: Ix)  -> Desc Ix

  ||| An argument to the constructor.
  |||
  ||| @ A the constructor field type
  ||| @ kdesc a further description, dependent on an argument of type `A`
  Arg : {Ix: _} -> (A: Type) -> (kdesc: (a: A) -> Desc Ix) -> Desc Ix

  ||| A recursive instantiation of the family at some particular index.
  Rec : {Ix: _} -> (ix: Ix)  -> (kdesc: Desc Ix) -> Desc Ix

%name Desc d, desc

CtorLabel : Type
CtorLabel = String

||| A set of labels that give the names of the constructors for a datatype
CtorEnum : Type
CtorEnum = List CtorLabel

||| A `Tag` selects a specific label from a label set
data Tag : CtorLabel -> CtorEnum -> Type where
  Z : {l, e: _}    ->  Tag l (l :: e)
  S : {l, l', e: _} -> Tag l e -> Tag l (l' :: e)

implementation Uninhabited (Tag _ []) where
  uninhabited Z impossible
  uninhabited (S t') impossible

||| A set of constructors, tagged by their names, is a function from
||| labels in the name set to data descriptions.
|||
||| ```idris example
||| TaggedDesc ["::", "Nil"] ()
||| ```
|||
||| @ e the constructors of the datatype
||| @ Ix the index set
TaggedDesc : (e: CtorEnum) -> (Ix: Type) -> Type
TaggedDesc e Ix = (l: CtorLabel) -> Tag l e -> Desc Ix

||| We can represent a datatype as a single constructor, where the
||| first argument selects which constructor we have, and uses that to
||| compute the remaining arguments.
|||
||| ```idris example
||| Untag {e=["::", "Nil"]} {Ix=()} (\l, t => Ret ())
||| ```
|||
||| @ e the set of constructor labels
||| @ d the tagged description
Untag : {e, Ix: _} -> (d : TaggedDesc e Ix) -> Desc Ix
Untag {e} d = Arg CtorLabel (\l => Arg (Tag l e) (\t => d l t))

||| Interpret a constructor description as a datatype.
|||
||| The call will almost always look like `Synthesize d (Data d)`.
|||
||| @ d the description
||| @ X the translated description, to "tie the recursive knot"
Synthesize : {Ix: _} -> (d : Desc Ix) -> (X : Ix -> Type) -> (Ix -> Type)
Synthesize (Ret ix)       X jx = ix ~=~ jx
Synthesize (Arg A kdesc)  X jx = (a: A ** Synthesize (kdesc a) X jx)
Synthesize (Rec ix kdesc) X jx = (x: X ix ** Synthesize kdesc X jx)

||| Translated descriptions, used mutually with `Synthesize`.
|||
||| ```idris example
||| let strVectDesc = Arg Bool (\b => if b then Arg String (\s => Arg Nat (\n => Rec n (Ret (S n)))) else Ret Z)
||| in Synthesize strVectDesc (Data strVectDesc)
||| ```
||| @ d a description of a family indexed over `Ix`
||| @ ix the particular index at which the datatype is instantiated
data Data : {Ix: Type} -> (d : Desc Ix) -> (ix : Ix) -> Type where
  Con : {Ix: _} -> {d : Desc Ix} -> {ix : Ix} -> Synthesize d (Data d) ix -> Data d ix

||| Descriptions of indexed families with parameters.
|||
||| @ n the number of parameters to the family
||| @ Ix the index set
data PDesc : (n : Nat) -> (Ix : Type) -> Type where
  ||| Instantiate at a particular element of the index set. See `Ret`.
  PRet  : {n,Ix: _} -> (ix: Ix)  -> PDesc n Ix
  ||| Take an argument. See `Arg`.
  PArg  : {n,Ix: _} -> (A: Type) -> (kdesc: (a: A) -> PDesc n Ix) -> PDesc n Ix
  ||| Select a particular parameter.
  PPar  : {n,Ix: _} -> (k : Fin n) -> (kdesc: PDesc n Ix) -> PDesc n Ix
  ||| Compute an argument type from one of the parameter types.
  PMap  : {n,Ix: _} -> (f : Type -> Type) -> (k : Fin n) -> (kdesc: PDesc n Ix) -> PDesc n Ix
  ||| Recur. See `Rec`.
  PRec  : {n,Ix: _} -> (ix: Ix)  -> (kdesc: PDesc n Ix) -> PDesc n Ix

||| Use a particular parameter type for a parameterized family description.
PUnfold : {n, Ix: _} -> PDesc (S n) Ix -> Type -> PDesc n Ix
PUnfold (PRet ix) = \B => PRet ix
PUnfold (PArg A kdesc) = \B => PArg A (\a : A => PUnfold (kdesc a) B)
PUnfold (PPar FZ kdesc) = \B => PArg B (\_ => PUnfold kdesc B)
PUnfold (PPar (FS k) kdesc) = \B => PPar k (PUnfold kdesc B)
PUnfold (PMap F FZ kdesc) = \B => PArg (F B) (\_ => PUnfold kdesc B)
PUnfold (PMap F (FS k) kdesc) = \B => PMap F k (PUnfold kdesc B)
PUnfold (PRec ix kdesc) = \B => PRec ix (PUnfold kdesc B)

||| When all parameters in a PDesc have been filled out, it can be
||| represented as an ordinary `Desc`.
PDescToDesc : {Ix : Type} -> PDesc Z Ix -> Desc Ix
PDescToDesc (PRet ix) = Ret ix
PDescToDesc (PArg A kdesc) = Arg A (\a => PDescToDesc (kdesc a))
PDescToDesc (PPar k kdesc) = absurd k
PDescToDesc (PMap f k kdesc) = absurd k
PDescToDesc (PRec ix kdesc) = Rec ix (PDescToDesc kdesc)

||| A version of `Synthesize` for parameterized families.
PSynthesize : {n, Ix: _} -> PDesc n Ix -> FunTy (replicate n Type) ((Ix -> Type) -> (Ix -> Type))
PSynthesize {n = Z} x = Synthesize (PDescToDesc x)
PSynthesize {n = (S k)} x = \a => PSynthesize (PUnfold x a)

||| A version of `Data` for parameterized datatypes.
|||
||| When there are no paramters, it is equivalent to `Data`, and when
||| there are n parameters, the result is an n-argument function that
||| will result in something equivalent to `Data` when the parameters
||| are instantiated.
PData : {n, Ix: _} -> PDesc n Ix -> FunTy (replicate n Type) (Ix -> Type)
PData {n = Z} x = Data (PDescToDesc x)
PData {n = (S k)} x = \a => PData (PUnfold x a)

||| A version of `Data` for tagged descriptions.
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
