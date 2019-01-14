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
||| @ ixty the type over which the family is indexed
data Desc : (ixty: Type) -> Type where

  ||| The final constructor description, instantiating the family at a
  ||| particular index.
  Ret : {ixty: _} -> (ix: ixty)  -> Desc ixty

  ||| An argument to the constructor.
  |||
  ||| @ A the constructor field type
  ||| @ kdesc a further description, dependent on an argument of type `A`
  Arg : {ixty: _} -> (A: Type) -> (kdesc: A -> Desc ixty) -> Desc ixty

  ||| A recursive instantiation of the family at some particular index.
  Rec : {ixty: _} -> (ix: ixty)  -> (kdesc: Desc ixty) -> Desc ixty

%name Desc d, desc

CtorLabel : Type
CtorLabel = TTName

||| A set of labels that give the names of the constructors for a datatype
CtorEnum : Type
CtorEnum = List CtorLabel

enumSize : CtorEnum -> Nat
enumSize = length

||| A `Tag` selects a specific label from a label set
data Tag : CtorLabel -> CtorEnum -> Type where
  Z : {l, e: _}    ->  Tag l (l :: e)
  S : {l, l', e: _} -> Tag l e -> Tag l (l' :: e)

%name Tag t, t'

implementation Uninhabited (Tag _ []) where
  uninhabited  Z    impossible
  uninhabited (S _) impossible

||| Pick a value from the given `choices` depending on the value of the selected label given by `tag`
|||
||| ```idris example
||| isNil = switch {e = ["::", "Nil"]} [False, True]
|||```
||| @ choices A list of values with the same size as the input set of labels, so there is a value for each label
||| @ tag The selected label
switch : {l,a: _} -> {e : CtorEnum} -> (choices: Vect (length e) a) -> (tag: Tag l e) -> a
switch {e = _ :: _} (c :: _)   Z    = c
switch {e = _ :: _} (_ :: cs) (S t) = switch cs t

||| A set of constructors, tagged by their names, is a function from
||| labels in the name set to data descriptions.
|||
||| ```idris example
||| TaggedDesc ["::", "Nil"] ()
||| ```
|||
||| @ e the constructors of the datatype
||| @ ixty the index set
TaggedDesc : (e: CtorEnum) -> (ixty: Type) -> Type
TaggedDesc e ixty = (l: CtorLabel) -> Tag l e -> Desc ixty

||| We can represent a datatype as a single constructor, where the
||| first argument selects which constructor we have, and uses that to
||| compute the remaining arguments.
|||
||| ```idris example
||| Untag {e=["::", "Nil"]} {ixty=()} (\l, t => Ret ())
||| ```
|||
||| @ e the set of constructor labels
||| @ d the tagged description
Untag : {e, ixty: _} -> (d : TaggedDesc e ixty) -> Desc ixty
Untag {e} d = Arg CtorLabel (\l => Arg (Tag l e) (\t => d l t))

||| Interpret a constructor description as a datatype.
|||
||| The call will almost always look like `Synthesize d (Data d)`.
|||
||| @ d the description
||| @ xty the translated description, to "tie the recursive knot"
Synthesize : {ixty: _} -> (d : Desc ixty) -> (xty : ixty -> Type) -> (ixty -> Type)
Synthesize (Ret ix)       xty jx = ix ~=~ jx
Synthesize (Arg g kdesc)  xty jx = (a: g ** Synthesize (kdesc a) xty jx)
Synthesize (Rec ix kdesc) xty jx = (x: xty ix ** Synthesize kdesc xty jx)

||| Translated descriptions, used mutually with `Synthesize`.
|||
||| ```idris example
||| let strVectDesc = Arg Bool (\b => if b then Arg String (\s => Arg Nat (\n => Rec n (Ret (S n)))) else Ret Z)
||| in Synthesize strVectDesc (Data strVectDesc)
||| ```
||| @ d a description of a family indexed over `ixty`
||| @ ix the particular index at which the datatype is instantiated
data Data : {ixty: Type} -> (d : Desc ixty) -> (ix : ixty) -> Type where
  Con : {ixty: _} -> {d : Desc ixty} -> {ix : ixty} -> Synthesize d (Data d) ix -> Data d ix

||| Descriptions of indexed families with parameters.
|||
||| @ n the number of parameters to the family
||| @ ixty the index set
data PDesc : (n : Nat) -> (ixty : Type) -> Type where
  ||| Instantiate at a particular element of the index set. See `Ret`.
  PRet  : {n,ixty: _} -> (ix: ixty)  -> PDesc n ixty
  ||| Take an argument. See `Arg`.
  PArg  : {n,ixty: _} -> (A: Type) -> (kdesc: A -> PDesc n ixty) -> PDesc n ixty
  ||| Select a particular parameter.
  PPar  : {n,ixty: _} -> (k : Fin n) -> (kdesc: PDesc n ixty) -> PDesc n ixty
  ||| Compute an argument type from one of the parameter types.
  PMap  : {n,ixty: _} -> (f : Type -> Type) -> (k : Fin n) -> (kdesc: PDesc n ixty) -> PDesc n ixty
  ||| Recur. See `Rec`.
  PRec  : {n,ixty: _} -> (ix: ixty)  -> (kdesc: PDesc n ixty) -> PDesc n ixty

||| Use a particular parameter type for a parameterized family description.
PUnfold : {n, ixty: _} -> PDesc (S n) ixty -> Type -> PDesc n ixty
PUnfold (PRet ix)               = \_ => PRet ix
PUnfold (PArg aty kdesc)        = \bty => PArg aty (\a : aty => PUnfold (kdesc a) bty)
PUnfold (PPar  FZ    kdesc)     = \bty => PArg bty (\_ => PUnfold kdesc bty)
PUnfold (PPar (FS k) kdesc)     = \bty => PPar k (PUnfold kdesc bty)
PUnfold (PMap fty  FZ    kdesc) = \bty => PArg (fty bty) (\_ => PUnfold kdesc bty)
PUnfold (PMap fty (FS k) kdesc) = \bty => PMap fty k (PUnfold kdesc bty)
PUnfold (PRec ix kdesc)         = \bty => PRec ix (PUnfold kdesc bty)

||| When all parameters in a PDesc have been filled out, it can be
||| represented as an ordinary `Desc`.
PDescToDesc : {ixty : Type} -> PDesc Z ixty -> Desc ixty
PDescToDesc (PRet ix)         = Ret ix
PDescToDesc (PArg aty kdesc)  = Arg aty (\a => PDescToDesc (kdesc a))
PDescToDesc (PPar k _)        = absurd k
PDescToDesc (PMap _ k _)      = absurd k
PDescToDesc (PRec ix kdesc)   = Rec ix (PDescToDesc kdesc)

||| A version of `Synthesize` for parameterized families.
PSynthesize : {n, ixty: _} -> PDesc n ixty -> FunTy (replicate n Type) ((ixty -> Type) -> (ixty -> Type))
PSynthesize {n = Z}   x = Synthesize (PDescToDesc x)
PSynthesize {n = S _} x = \a => PSynthesize (PUnfold x a)

||| A version of `Data` for parameterized datatypes.
|||
||| When there are no paramters, it is equivalent to `Data`, and when
||| there are n parameters, the result is an n-argument function that
||| will result in something equivalent to `Data` when the parameters
||| are instantiated.
PData : {n, ixty: _} -> PDesc n ixty -> FunTy (replicate n Type) (ixty -> Type)
PData {n = Z}   x = Data (PDescToDesc x)
PData {n = S _} x = \a => PData (PUnfold x a)

PTaggedDesc : (e: CtorEnum) -> (n : Nat) -> (ixty : Type) -> Type
PTaggedDesc e n ixty = (l : CtorLabel) -> Tag l e -> PDesc n ixty

PUntag : {e, n, ixty : _} -> PTaggedDesc e n ixty -> PDesc n ixty
PUntag {e} d = PArg CtorLabel (\l => PArg (Tag l e) (\t => d l t))

||| A version of `Data` for tagged descriptions.
TaggedData : {ixty: _} -> {e: CtorEnum} -> TaggedDesc e ixty -> (ixty -> Type)
TaggedData d = Data (Untag d)

PTaggedData : {ixty,n: _} -> {e: CtorEnum} -> PTaggedDesc e n ixty -> FunTy (replicate n Type) (ixty -> Type)
PTaggedData d = PData (PUntag d)

Constraints : {ixty: _} -> (Interface: Type -> Type) -> (d: Desc ixty) -> Type
Constraints _         (Ret _)       = Unit
Constraints interfaceTy (Arg f kdesc) = (interfaceTy f, (a: f) -> Constraints interfaceTy (kdesc a))
Constraints interfaceTy (Rec _ kdesc) = Constraints interfaceTy kdesc

TaggedConstraints : {e, ixty: _} -> (interfaceTy: Type -> Type) -> (td: TaggedDesc e ixty) -> Type
TaggedConstraints {e} interfaceTy td = (l : CtorLabel) -> (t : Tag l e) -> Constraints interfaceTy (td l t)

PConstraints1 : {ixty: _} -> (interfaceTy : (Type -> Type) -> Type) -> (d: PDesc (S Z) ixty) -> Type
PConstraints1 _         (PRet _)         = ()
PConstraints1 interfaceTy (PArg f kdesc)   = (a : f) -> PConstraints1 interfaceTy (kdesc a)
PConstraints1 interfaceTy (PPar _ kdesc)   = PConstraints1 interfaceTy kdesc
PConstraints1 interfaceTy (PMap f _ kdesc) = (interfaceTy f, PConstraints1 interfaceTy kdesc)
PConstraints1 interfaceTy (PRec _ kdesc)   = PConstraints1 interfaceTy kdesc

PTaggedConstraints1 : {e, ixty: _} -> (interfaceTy : (Type -> Type) -> Type) -> (td: PTaggedDesc e (S Z) ixty) -> Type
PTaggedConstraints1 {e} interfaceTy td = (l : CtorLabel) -> (t : Tag l e) -> PConstraints1 interfaceTy (td l t)
