module Descriptions.Automation

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

