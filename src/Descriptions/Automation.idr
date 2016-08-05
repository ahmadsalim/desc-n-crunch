module Descriptions.Automation

import Language.Reflection.Utils
import Descriptions.Core
import Pruviloj

ctorTags : TTName -> Elab (List TTName)
ctorTags datatype =
  do ctors <- constructors <$> lookupDatatypeExact datatype
     pure $ map fst ctors


genCtorEnum : (datatype, enum : TTName) -> Elab ()
genCtorEnum datatype enum =
  do tags <- ctorTags datatype
     declareType $ Declare enum [] (Var `{CtorEnum})
     defineFunction $ DefineFun enum [MkFunClause (Var enum) (quote tags)]


ns : TTName -> TTName
ns n = NS n ["Automation", "Descriptions"]

%runElab (genCtorEnum `{Nat} (ns `{{NatCtors}}))


fromTag : Vect (enumSize e) a -> Tag l e -> a
fromTag (x :: _)  Z = x
fromTag (_ :: xs) (S t) = fromTag xs t

foo : Datatype
foo = %runElab ((quote <$> lookupDatatypeExact `{Vect.Vect}) >>= exact)

getIndices : TTName -> List TyConArg -> Raw -> Elab (List (Raw, Raw))
getIndices tyN tcArgs tm =
  do let (op, args) = unApply tm
     -- Sanity check
     case op of
       Var n => if n == tyN
                  then return ()
                  else fail [TextPart "Wrong datatype: ", NamePart n]
       other => fail [TextPart "Not a datatype application"]
     getArgs args tcArgs
  where getArgs : List Raw -> List TyConArg -> Elab (List (Raw, Raw))
        getArgs [] [] =
          pure []
        getArgs [] (x :: xs) =
          fail [TextPart "Argument mismatch"]
        getArgs (x :: xs) [] =
          fail [TextPart "Argument mismatch"]
        getArgs (x :: xs) (TyConParameter y :: ys) =
          getArgs xs ys
        getArgs (x :: xs) (TyConIndex y     :: ys) =
          ((x, type y) ::) <$> getArgs xs ys

prod : List Raw -> Raw
prod [] = `(() : Type)
prod [x] = x
prod (x :: xs) = `((~x, ~(prod xs)) : Type)

prodElem : List (Raw, Raw) -> Raw
prodElem [] = `(():())
prodElem [(x, t)] = x
prodElem ((x, t) :: xs) =
  `(MkPair {A=~t} {B=~(prod (map snd xs))}
           ~x ~(prodElem xs))

paramCount : List TyConArg -> Nat
paramCount [] = 0
paramCount (TyConParameter x :: xs) = S (paramCount xs)
paramCount (TyConIndex x     :: xs) = paramCount xs

findParam : FunArg -> Raw -> Elab Nat
findParam x tm =
  do let (op, args) = unApply tm
     let pn = name x
     case findIndex (isVar (name x)) args of
       Nothing => empty
       Just j  => pure j

  where isVar : TTName -> Raw -> Bool
        isVar n (Var m) = n == m
        isVar _ _ = False

mkFin : (k, bound : Nat) -> Elab Raw
mkFin k Z = empty
mkFin Z (S bound') = pure `(FZ {k=~(quote bound')})
mkFin (S k) (S bound') = do i <- mkFin k bound'
                            pure `(FS {k=~(quote bound')} ~i)

isRec : TTName -> Raw -> Bool
isRec tyn tm = case fst (unApply tm) of
                 Var n => tyn == n
                 _ => False

containsParam : List TTName -> Raw -> Bool
containsParam ps (Var n) = n `elem` ps
containsParam ps (RBind n b tm) = binderContains b || containsParam (filter (==n) ps) tm
  where binderContains : Binder Raw -> Bool
        binderContains b =
          foldr (\x,y => x || y) False $ map (containsParam ps) b
containsParam ps (RApp tm tm') = containsParam ps tm || containsParam ps tm'
containsParam ps RType = False
containsParam ps (RUType x) = False
containsParam ps (RConstant c) = False


mkDesc : TTName -> List TTName -> List TyConArg -> (TTName, List CtorArg, Raw) -> Elab Raw
mkDesc tyn paramsSoFar tcArgs (cn, [], cRes) =
  do indices <- getIndices tyn tcArgs cRes
     pure `(PRet {n=~(quote (paramCount tcArgs))}
                 {Ix=~(prod (map snd indices))}
                  ~(prodElem indices))
mkDesc tyn paramsSoFar tcArgs (cn, cArg::cArgs, cRes) =
     case cArg of
       CtorParameter arg =>
         do which <- findParam arg cRes
            rest <- mkDesc tyn (name arg :: paramsSoFar) tcArgs (cn, cArgs, cRes)
            let n = paramCount tcArgs
            i <- mkFin which n
            indices <- getIndices tyn tcArgs cRes
            pure `(PPar {n=~(quote n)} {Ix=~(prod (map snd indices))} ~i ~rest)
       CtorField arg =>
         -- A field can be either a transformed parameter, a recursive
         -- instantiation, or an ordinary argument.
         if containsParam paramsSoFar (type arg)
           then debugMessage [TextPart "Not done yet!", TextPart (show arg)]
           else
             if isRec tyn (type arg)
               then
                 do recIndices <- getIndices tyn tcArgs (type arg)
                    resIndices <- getIndices tyn tcArgs cRes
                    let n = paramCount tcArgs
                    rest <- mkDesc tyn paramsSoFar tcArgs (cn, cArgs, cRes)

                    pure `(PRec {n=~(quote n)}
                                {Ix=~(prod (map snd resIndices))}
                                ~(prodElem recIndices)
                                ~rest)
               else -- normal arg
                 do indices <- getIndices tyn tcArgs cRes
                    let n = paramCount tcArgs
                    rest <- mkDesc tyn paramsSoFar tcArgs (cn, cArgs, cRes)
                    pure `(PArg {n=~(quote n)}
                                {Ix=~(prod (map snd indices))}
                                ~(type arg)
                                ~(RBind (name arg)
                                        (Lam (type arg))
                                        rest))

s : PDesc 0 ()
s = %runElab (do fill !(mkDesc `{Nat} [] [] (`{Nat.S}, [CtorField $ MkFunArg `{{n}} `(Nat) Explicit NotErased], `(Nat)))
                 solve)

z : PDesc 0 ()
z = %runElab (do fill !(mkDesc `{Nat} [] [] (`{Nat.Z}, [], `(Nat)))
                 solve)

nil : PDesc 1 ()
nil = %runElab (do fill !(mkDesc `{List} [] [ TyConParameter $ MkFunArg `{{a}} `(Type) Implicit Erased] (`{List.Nil}, [CtorParameter $ MkFunArg `{{a}} `(Type) Implicit Erased], `(List ~(Var `{{a}}))))
                   solve)

cons : PDesc 1 ()
cons = %runElab (do fill !(mkDesc `{List} [] [ TyConParameter $ MkFunArg `{{a}} `(Type) Implicit Erased] (`{List.(::)}, [CtorParameter $ MkFunArg `{{a}} `(Type) Implicit Erased, CtorField $ MkFunArg `{{x}} (Var `{{a}}) Explicit NotErased, CtorField $ MkFunArg `{{xs}} `(List ~(Var `{{a}})) Explicit NotErased], `(List ~(Var `{{a}}))))
                    solve)
