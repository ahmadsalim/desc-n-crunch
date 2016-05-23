module Helper

import public Data.Vect
import public Data.Fin
import public Data.So

%default total

public export
FunTy : .{n : Nat} -> (argtys : Vect n Type) -> (rty : Type) -> Type
FunTy [] rty = rty
FunTy (argty :: argtys) rty = argty -> FunTy argtys rty

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
