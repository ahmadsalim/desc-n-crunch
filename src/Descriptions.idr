module Descriptions

import Language.Reflection
import Language.Reflection.Errors
import Language.Reflection.Utils

import Pruviloj
import Pruviloj.Internals


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
resolveTCPlus' : Nat -> List TTName -> Elab () -> Elab ()
resolveTCPlus' Z _ _ =
  fail [TextPart "Search failed because the depth limit was reached."]
resolveTCPlus' (S k) tns tac =
  do attack
     try $ repeatUntilFail intro'
     case headName !goalType of
       Nothing => tac
       Just n =>
         if not (n `elem` tns)
           then tac
           else do ctors <- constructors <$> lookupDatatypeExact n
                   choice (map (\(cn, args, _) =>
                                 applyCtor cn (length args) (resolveTCPlus' k tns tac))
                               ctors)
     solve -- the attack

covering
resolveTCPlus : Elab ()
resolveTCPlus = resolveTCPlus' 100 [`{Unit}, `{Pair}] (resolveTC `{resolveTCPlus})

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

---- Examples
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

-- TODO: Ask David about help automating this even more
VecShowConstraints : {A : Type} -> (Show A) => TaggedConstraints Show (VecDesc A)
VecShowConstraints = \l, t =>
  case t of
    Z => %runElab resolveTCPlus
    S Z => %runElab resolveTCPlus
    S (S Z) impossible

exampleVecShown : gshow (VecDesc String) (VecShowConstraints {A = String}) exampleVec = """Cons 1 "Hello" (Cons 0 "World" Nil)"""
exampleVecShown = Refl
