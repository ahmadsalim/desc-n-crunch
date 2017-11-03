module Descriptions.Show
import Descriptions.Core

%default total
%access export
%auto_implicits off

parenthesize : String -> String
parenthesize str = if length (words str) <= 1 then str else "(" ++ str ++ ")"

showLabel : TTName -> String
showLabel (UN n) with (strM n)
  showLabel (UN "")             | StrNil = ""
  showLabel (UN (strCons x xs)) | StrCons x xs =
    if isAlpha x then strCons x xs else "(" ++ strCons x xs ++ ")"
showLabel (NS n xs) = concat (intersperse "." (reverse xs)) ++ "." ++ showLabel n
showLabel (MN x y) = "{" ++ y ++ show x ++ "}"
showLabel (SN _) = "{{SN}}"

mutual
  gshowd : {e, Ix: _} -> (dR: TaggedDesc e Ix) -> (cstrsR: TaggedConstraints Show dR)
                      -> (d: Desc Ix) -> (cstrs: Constraints Show d)
                      -> {ix: Ix} -> (synth: Synthesize d (TaggedData dR) ix)
                      -> String
  gshowd _  _            (Ret _) () Refl = ""
  gshowd dR cstrsR (Arg _ kdesc) (showa, showkdesc) (arg ** rest) =
    " " ++ parenthesize (show @{showa} arg)
        ++ gshowd dR cstrsR (kdesc arg) (showkdesc arg) rest
  gshowd dR cstrsR (Rec _ kdesc) cstrs (rec ** rest) =
    " " ++ parenthesize (gshow dR cstrsR rec)
        ++ gshowd dR cstrsR kdesc cstrs rest

  gshow : {e, Ix: _} -> (d: TaggedDesc e Ix) -> (cstrs: TaggedConstraints Show d)
                    -> {ix : Ix} -> (X : TaggedData d ix) -> String
  gshow d cstrs (Con (label ** tag ** rest)) =
    let cstrs' = cstrs label tag
        showrest = assert_total $ gshowd d cstrs (d label tag) cstrs' rest
    in showLabel label ++ showrest
