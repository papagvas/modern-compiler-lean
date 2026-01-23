import Lean

open Lean

namespace Tiger.Location
  
  inductive SrcLoc where
    | fromFile (left : Position) (right : Position)
    | std
    | unknown
  deriving Repr, BEq

instance : ToString SrcLoc where
  toString srcLoc := match srcLoc with
    | .fromFile l r => s!"{l}-{r}"
    | .std => "Prelude"
    | .unknown => "Unknown location"

  def toSrcLoc (fm : FileMap) (stx : Syntax) : SrcLoc := 
    let l := stx.getPos?
    let r := stx.getTailPos?
    match l, r with
      | none, none | none, _ | _, none => .unknown
      | some left, some right => .fromFile (fm.toPosition left) (fm.toPosition right) 

end Tiger.Location
