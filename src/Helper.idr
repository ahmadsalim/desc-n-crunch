module Helper

import public Data.Vect
import public Data.Fin
import public Data.So

%default total

||| Given a vector of argument types and a return type, generate the
||| corresponding non-dependent function type.
|||
||| ```idris example
||| FunTy [Nat, String, ()] Integer
||| ```
public export
FunTy : .{n : Nat} -> (argtys : Vect n Type) -> (rty : Type) -> Type
FunTy [] rty = rty
FunTy (argty :: argtys) rty = argty -> FunTy argtys rty

||| Compose two functions whose argument types are described using
||| `Vect`.
|||
||| ```idris example
||| (composeFun {argtys = [Nat, Integer]} {rty=Int} {argtys'=[String]} {rty'=Nat} (\x,y => 4) (\i, str => cast i + length str)) Z 3 "fnord"
||| ```
public export
composeFun : {argtys, rty, argtys', rty' : _} -> FunTy argtys rty -> FunTy (rty::argtys') rty' -> FunTy (argtys ++ argtys') rty'
composeFun {argtys = []} v g = g v
composeFun {argtys = _ :: _} f g = \x => composeFun (f x) g

export
soToEq : So b -> b = True
soToEq Oh = Refl

export
eqToSo : b = True -> So b
eqToSo Refl = Oh

export
soNotSo : So (not b) -> So b -> Void
soNotSo Oh Oh impossible

export
notSoSo : (So b -> Void) -> So (not b)
notSoSo {b} contra with (choose b)
  notSoSo contra | (Left so) = void (contra so)
  notSoSo contra | (Right notso) = notso

export
soAndSo : So (a && b) -> (So a, So b)
soAndSo {a} {b} soand with (choose a)
  soAndSo {a = True}  soand | Left Oh = (Oh, soand)
  soAndSo {a = False} Oh    | Right Oh impossible
  soAndSo {a = True}  Oh    | Right Oh impossible

export
andSoSo : So a -> So b -> So (a && b)
andSoSo Oh sob = sob

export
soOrSo : So (a || b) -> Either (So a) (So b)
soOrSo {a} {b} soor with (choose a)
  soOrSo {a = True}  _    | Left Oh = Left Oh
  soOrSo {a = False} _    | Left Oh impossible
  soOrSo {a = False} soor | Right Oh = Right soor
  soOrSo {a = True}  _    | Right Oh impossible

export
orSoSo : Either (So a) (So b) -> So (a || b)
orSoSo (Left Oh) = Oh
orSoSo {a = False} (Right Oh) = Oh
orSoSo {a = True} (Right Oh) = Oh

export
dpairEq : {a: Type} -> {P: a -> Type} -> {x, x' : a} -> {y : P x} -> {y' : P x'} -> (p : x = x') -> y = y' -> (x ** y) = (x' ** y')
dpairEq Refl Refl = Refl

export
dpairFstInjective : {x,y,xs,ys: _} -> (x ** xs) = (y ** ys) -> x = y
dpairFstInjective Refl = Refl

export
dpairSndInjective : {x,y,xs,ys: _} -> (x ** xs) = (y ** ys) -> xs = ys
dpairSndInjective Refl = Refl

export
unitEta : {x : Unit} -> x = ()
unitEta {x = ()} = Refl

export
pairEta : {x : (a, b)} -> x = (fst x, snd x)
pairEta {x = (y, z)} = Refl

export
dpairEta : {x : (a ** b)} -> x = (fst x ** snd x)
dpairEta {x = (y ** z)} = Refl

postulate export -- Should be OK
  funext : {a,b : Type} -> {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

export
fundet : {a, b : Type} -> {f, g : a -> b} -> f = g -> (x : a) -> f x = g x
fundet {f} {g = f} Refl x = Refl

export
Uninhabited (Left _ = Right _) where
  uninhabited Refl impossible

export
Uninhabited (Right _ = Left _) where
  uninhabited Refl impossible
