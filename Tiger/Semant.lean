import Std.Data.HashMap
import Std.Data.HashSet
import Tiger.Semant.Types
import Tiger.AST
import Tiger.Location

open Std
open Tiger.Semant.Types
open Tiger.Location

namespace Tiger.Semant

  def transTy (astTy : Tiger.AST.Kind .parse) : SemantM Ty :=
    match astTy with
      | .typeId (pos : SrcLoc) ident => do
        let (tenv, _) ← read 
        match tenv.get? ident.name with
          | some ty => pure ty
          | none    => throw s!"{pos}: {ident} is not defined"
      | .typeMap (pos : SrcLoc) tm => do
        let recs ← tm.foldlM (λ (recs', (set : HashSet String)) {name := n, field := f} => do
          let (tenv, _) ← read
          match tenv.get? f.name, set.containsThenInsert n.name with
            | _ , (false, _) => throw s!"{pos}: {n} is already defined"
            | none, _ => throw s!"{pos}: {f} is not defined"
            | some ty, (true, set') => pure ((n.name, ty) :: recs', set')) ({}, {})
        let uid ← getUnique
        pure $ .record recs.1.reverse uid
      | .arrayType (pos : SrcLoc) ident => do
        let (tenv, _) ← read
        match tenv.get? ident.name with
          | some ty => pure $ .array ty (← getUnique)
          | none    => throw s!"{pos}: {ident} is not defined"
 
end Tiger.Semant
