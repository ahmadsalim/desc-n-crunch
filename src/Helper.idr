module Helper

import public Data.Vect
import public Data.Fin

public export
FunTy : .{n : Nat} -> (argtys : Vect n Type) -> (rty : Type) -> Type
FunTy [] rty = rty
FunTy (argty :: argtys) rty = argty -> FunTy argtys rty

public export
composeFun : {argtys, rty, argtys', rty' : _} -> FunTy argtys rty -> FunTy (rty::argtys') rty' -> FunTy (argtys ++ argtys') rty'
composeFun {argtys = []} v g = g v
composeFun {argtys = (x :: xs)} f g = \x => composeFun (f x) g
