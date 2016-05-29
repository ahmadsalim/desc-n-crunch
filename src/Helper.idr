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
composeFun {argtys = (x :: xs)} f g = \x => composeFun (f x) g

public export
soToEq : So b -> b = True
soToEq Oh = Refl

public export
eqToSo : b = True -> So b
eqToSo Refl = Oh

public export
soNotSo : So b -> So (not b) -> Void
soNotSo Oh Oh impossible

public export
soAndSo : So (a && b) -> (So a, So b)
soAndSo {a} {b} soand with (choose a)
  soAndSo {a = True} {b = b} soand | (Left Oh) = (Oh, soand)
  soAndSo {a = False} {b = _} Oh | (Right Oh) impossible
  soAndSo {a = True} {b = _} Oh | (Right Oh) impossible

public export
soOrSo : So (a || b) -> Either (So a) (So b)
soOrSo {a} {b} soor with (choose a)
  soOrSo {a = True} {b = b} soor | (Left Oh) = Left Oh
  soOrSo {a = False} {b = b} soor | (Left Oh) impossible
  soOrSo {a = False} {b = b} soor | (Right Oh) = Right soor
  soOrSo {a = True} {b = b} soor | (Right Oh) impossible

public export
dpairEq : {a: Type} -> {P: a -> Type} -> {x, x' : a} -> {y : P x} -> {y' : P x'} -> (p : x = x') -> y = y' -> (x ** y) = (x' ** y')
dpairEq Refl Refl = Refl

postulate -- HOPEFULLY NOTHING GOES WRONG
  public export
  funext : {a,b : Type} -> {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

public export
fundet : {a, b : Type} -> {f, g : a -> b} -> f = g -> (x : a) -> f x = g x
fundet {f = f} {g = f} Refl x = Refl
