module Descriptions.Tactical

import Language.Reflection
import Language.Reflection.Errors
import Language.Reflection.Utils

import Pruviloj
import Pruviloj.Internals

%default total
%access export

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
dfsearch : Nat -> List TTName -> Elab () -> Elab ()
dfsearch Z _ _ =
  fail [TextPart "Search failed because the depth limit was reached."]
dfsearch (S k) tns tac =
  do attack
     try $ repeatUntilFail intro'
     case headName !goalType of
       Nothing => tac
       Just n =>
         if not (n `elem` tns)
           then tac
           else do ctors <- constructors <$> lookupDatatypeExact n
                   choice (map (\(cn, args, _) =>
                                 applyCtor cn (length args) (dfsearch k tns tac))
                               ctors)
     solve -- the attack

covering
iddfsearch : Nat -> List TTName -> Elab () -> Elab ()
iddfsearch k tns tac = choice $ map (\i => dfsearch i tns tac) [0..k]

covering
resolveTCPlus : Elab ()
resolveTCPlus = iddfsearch 100 [`{Unit}, `{Pair}] (resolveTC `{resolveTCPlus})
