module Descriptions.Show
import Descriptions.Core

%default total
%access export
%auto_implicits off

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
