import Std.Data.HashMap
import Std.Data.HashSet
import Tiger.Semant.Types
import Tiger.AST
import Tiger.Location

open Std
open Tiger.Semant.Types
open Tiger.Location

namespace Tiger.Semant

  partial def actualTy (ty: Ty) : SemantM Ty := 
    match ty with
      | .name str ty? => match ty? with
        | some t => actualTy t
        | none   => do
          let tenv := (← read).tenv
          match tenv.get? str with
            | some t' => actualTy t'
            | none    => throw s!"{str} is not a valid type"
      | _ => pure ty

  def transTy (astTy : Tiger.AST.Kind .parse) : SemantM Ty := do
    let tenv := (← read).tenv
    match astTy with
      | .typeId (pos : SrcLoc) ident => do
        match tenv.get? ident.name with
          | some ty => pure ty
          | none    => throw s!"{pos}: {ident} is not defined"
      | .typeMap (pos : SrcLoc) tm => do
        let recs ← tm.foldlM (λ (recs', (set : HashSet String)) {name := n, field := f} => do
          match tenv.get? f.name, set.containsThenInsert n.name with
            | _ , (true, _) => throw s!"{pos}: {n} is already defined"
            | none, _ => throw s!"{pos}: {f} is not defined"
            | some ty, (false, set') => pure ((n.name, ty) :: recs', set')) ({}, {})
        let uid ← getUnique
        pure $ .record recs.1.reverse uid
      | .arrayType (pos : SrcLoc) ident => do
        match tenv.get? ident.name with
          | some ty => pure $ .array ty (← getUnique)
          | none    => throw s!"{pos}: {ident} is not defined"

  def loopVar? (lv : Tiger.AST.LValue .parse) : SemantM (Option Tiger.Semant.Types.ReadOnly) :=
    match lv with
      | .var (pos : SrcLoc) ident => do
        match (← read).venv.get? ident.name with
          | none => throw s!"{pos}: variable {ident} doesn't exist"
          | some entry => match entry with
            | .funEntry _ _ => throw s!"{pos}: expected a variable got a function"
            | .varEntry _ readOnly? => pure readOnly?
      | _ => pure none
  
  mutual

    partial def transExpr (expr : Tiger.AST.Expr .parse) : SemantM (Tiger.AST.Expr .semant) := 
      match expr with
        | .nil (pos : SrcLoc) => pure $ .nil (pos, .nil)
        | .breakE (pos : SrcLoc) => do
          match (← read).loop? with
            | .loop   => pure $ .breakE (pos, .unit)
            | .noLoop => throw s!"{pos}: break used outside of loop"
        | .intE (pos : SrcLoc) n => pure $ .intE (pos, .int) n  
        | .strE (pos : SrcLoc) s => pure $ .strE (pos, .string) s
        | .lvalueE (pos : SrcLoc) lv => do
          let lv' ← transLValue lv
          let (_, ty) := Tiger.AST.HasInfo.getInfo lv'
          pure $ .lvalueE (pos, ty) lv'
        | .binE (pos : SrcLoc) op l r => do
          let left ← transExpr l
          let right ← transExpr r
          let (posL, tyL) := Tiger.AST.HasInfo.getInfo left
          let (posR, tyR) := Tiger.AST.HasInfo.getInfo right
          match (← actualTy tyL) with
            | .int => match (← actualTy tyR) with
              | .int => pure $ .binE (pos, .int) op left right 
              | _    => throw s!"{posR}: expression should be int, got {tyR}"
            | _ => throw s!"{posL}: expression should be int, got {tyL}"
        | .compare (pos : SrcLoc) op l r => do
          let left ← transExpr l
          let right ← transExpr r
          let (posL, tyL) := Tiger.AST.HasInfo.getInfo left
          let (posR, tyR) := Tiger.AST.HasInfo.getInfo right
          match (← actualTy tyL), (← actualTy tyR) with
            | .int, .int => pure $ .compare (pos, .int) op left right 
            | .string, .string => pure $ .compare (pos, .string) op left right 
            | .int, .string | .string, .int => throw s!"{pos}: types of subexpressions do not match"
            | .int, _                       => throw s!"{posR}: expression should be int, got {tyR}"
            | .string, _                    => throw s!"{posR}: expression should be string, got {tyR}"
            | _, .int                       => throw s!"{posL}: expression should be int, got {tyL}"
            | _, .string                    => throw s!"{posL}: expression should be string, got {tyL}"
            | _, _                          => throw s!"{pos}: type mismatch, subexpressions should be int or string"
        | .negate (pos : SrcLoc) expr => do
          let e ← transExpr expr
          let (_, ty) := Tiger.AST.HasInfo.getInfo e
          match (← actualTy ty) with
            | .int => pure $ .negate (pos, .int) e 
            | ty'  => throw s!"{pos}: Subexpression should be of type int got"
        | .assign (pos : SrcLoc) lv e => do
          match (← loopVar? lv) with
            | some _ => throw s!"{pos}: you cannot assign a loop variable"
            | none => do
              let lvalue ← transLValue lv
              let expr   ← transExpr e
              let (_, tyL') := Tiger.AST.HasInfo.getInfo lvalue
              let (_, tyR') := Tiger.AST.HasInfo.getInfo expr
              let tyL ← actualTy tyL'
              let tyR ← actualTy tyR'
              if tyL == tyR
                then pure $ .assign (pos, tyL) lvalue expr
                else throw s!"{pos}: Types {tyL'} and {tyR'} don't match"
        | .seq (pos : SrcLoc) es => do
          match (← es.foldlM (λ es' e => do pure $ (← transExpr e) :: es') []) with
            | [] => pure $ .seq (pos, .unit) []
            | exprs@(expr :: tail) => do
              let (_, ty) := Tiger.AST.HasInfo.getInfo expr
              pure $ .seq (pos, ty) exprs.reverse
        | .ifThenElse (pos : SrcLoc) e1 e2 e3? => do
          let expr1 ← transExpr e1
          let (pos1, ty1) := Tiger.AST.HasInfo.getInfo expr1
          match (← actualTy ty1) with
            | .int => match e3? with
              | some e3 => do
                let expr2 ← transExpr e2
                let expr3 ← transExpr e3
                let (_, ty2) := Tiger.AST.HasInfo.getInfo expr2
                let (_, ty3) := Tiger.AST.HasInfo.getInfo expr3
                let trueType ← actualTy ty2
                if trueType == (← actualTy ty3)
                  then pure $ .ifThenElse (pos, trueType) expr1 expr2 (some expr3)
                  else throw s!"{pos}: Types of subexprs do not match, {ty2} ≠ {ty3}"
              | none => do
                let expr2 ← transExpr e2
                let (pos2, ty2) := Tiger.AST.HasInfo.getInfo expr2
                match (← actualTy ty2) with
                  | .unit => pure $ .ifThenElse (pos, .unit) expr1 expr2 none
                  | _     => throw s!"{pos2}: Expression should be of type unit, got {ty2}"
            | _    => throw s!"{pos1}: Condition should be of type int, got {ty1}"
        | .whileE (pos : SrcLoc) e1 e2 => withReader (λ scope => { scope with loop? := .loop }) $ do
          let expr1 ← transExpr e1
          let (pos1, ty1) := Tiger.AST.HasInfo.getInfo expr1
          match (← actualTy ty1) with
            | .int => do
              let expr2 ← transExpr e2
              let (pos2, ty2) := Tiger.AST.HasInfo.getInfo expr2
              match (← actualTy ty2) with
                | .unit => pure $ .whileE (pos, .unit) expr1 expr2
                | _     => throw s!"{pos2}: Body is supposed to have type unit, got {ty2}"
            | _   => throw s!"{pos1}: Condition is supposed to have type int, got {ty1}"
        | .forE (pos : SrcLoc) ident lo hi body => do
          let low ← transExpr lo
          let high ← transExpr hi
          let (posL, tyL) := Tiger.AST.HasInfo.getInfo low
          let (posH, tyH) := Tiger.AST.HasInfo.getInfo high
          match (← actualTy tyL), (← actualTy tyH) with
            | .int, .int => withReader (λ scope => { scope with venv := scope.venv.insert ident.name (.varEntry .int (some .readOnly)), loop? := .loop }) $ do
              let body' ← transExpr body
              let (posB, tyB) := Tiger.AST.HasInfo.getInfo body'
              match (← actualTy tyB) with
                | .unit => pure $ .forE (pos, .unit) ident low high body'
                | _     => throw s!"{posB}: Body should be unit, got {tyB}"
            | .int, _    => throw s!"{posH}: Expression should be int, got {tyH}"
            | _, .int    => throw s!"{posL}: Expression should be int, got {tyL}"
            | _, _       => throw s!"{pos}: Loop boundaries shoould be int"
        | .letE (pos : SrcLoc) ds e => do
          let decls ← transDecls ds
          let expr ← transExpr e
          let (_, ty) := Tiger.AST.HasInfo.getInfo expr
          pure $ .letE (pos, ty) decls expr
        | .funCall (pos : SrcLoc) ident es => do
          let venv := (← read).venv
          match venv.get? ident.name with
            | some entry => match entry with
              | .varEntry _ _ => throw s!"{pos}: expected a function not a variable"
              | .funEntry tys rt => do
                unless tys.length == es.length do
                  throw s!"{pos}: Number of arguments given does not match"
                let exprs ← (es.zip tys).mapM λ (e, ty) => do
                  let expr ← transExpr e
                  let (posE, tyE) := Tiger.AST.HasInfo.getInfo expr
                  if (← actualTy tyE) == ty
                    then pure expr
                    else throw s!"{posE}: Argument of a function has a wrong type: expected {ty} got {tyE}"
                pure $ .funCall (pos, rt) ident exprs
            | none => throw s!"{pos}: {ident} does not exist"
        | .record (pos : SrcLoc) ident es => do
          let tenv := (← read).tenv
          match tenv.get? ident.name with
            | some t => match t with
              | .record tys _ => do
                unless (es.length == tys.length) do
                  throw s!"{pos}: Number of arguments given does not match"
                let exprs ← (es.zip tys).mapM λ ({ name := n, field := e } , (str, ty)) => do
                  unless n.name == str do
                    throw s!"{pos}: expected field {str}, got {n}"
                  let expr ← transExpr e
                  let (pos1, t1) := Tiger.AST.HasInfo.getInfo expr 
                  if (← actualTy t1) == (← actualTy ty)
                    then pure { name := n, field := expr }
                    else throw s!"{pos1}: Types do not match: expected {ty}, got {t1}"
                pure $ .record (pos, t) ident exprs
              | _             => throw s!"{pos}: {ident} should be a record got {t}"
            | none   => throw s!"{pos}: {ident} is not defined"
        | .arrayE (pos : SrcLoc) ident e1 e2 => do
          let tenv := (← read).tenv
          match tenv.get? ident.name with
            | some t => match t with
              | .array ty _ => do
                let expr1 ← transExpr e1
                let (pos1, ty1) := Tiger.AST.HasInfo.getInfo expr1
                match (← actualTy ty1) with
                  | .int => do
                    let expr2 ← transExpr e2
                    let (pos2, ty2) := Tiger.AST.HasInfo.getInfo expr2
                    if (← actualTy ty2) == (← actualTy ty)
                      then pure $ .arrayE (pos, ty) ident expr1 expr2
                      else throw s!"{pos2}: Type mismatch, value should of type {ty}, got {ty2}"
                  | _    => throw s!"{pos1}: Type of the expression should be int, got {ty1}"
              | _ => throw s!"{pos}: Expected an array type, got {t}"
            | none   => throw s!"{pos}: {ident} is not defined"

    partial def transDecls (decls : List (Tiger.AST.Decls .parse)) : SemantM (List (Tiger.AST.Decls .semant)) := sorry

    partial def transLValue (lv : Tiger.AST.LValue .parse) : SemantM (Tiger.AST.LValue .semant) :=
      match lv with
        | .var (pos : SrcLoc) ident => do
          let venv := (← read).venv
          match venv.get? ident.name with
            | .some entry => match entry with
              | .varEntry ty _ => pure $ .var (pos, ty) ident
              | .funEntry _ _  => throw s!"{pos}: Expected a variable, got a function"
            | none => throw s!"{pos}: {ident} does not exist"
        | .field (pos : SrcLoc) lval fld => do
          let lvalue ← transLValue lval
          let (pos1, ty1) := Tiger.AST.HasInfo.getInfo lvalue
          match (← actualTy ty1) with
            | .record tys _ => match tys.lookup fld.name with
              | some ty => pure $ .field (pos, ty) lvalue fld
              | none    => throw s!"{pos}: {fld} does not exist"
            | _ => throw s!"{pos1}: Expected an lvalue of type record, got {ty1}"
        | .subscript (pos : SrcLoc) lval e => do
          let lvalue ← transLValue lval
          let (pos1, ty1) := Tiger.AST.HasInfo.getInfo lvalue
          match (← actualTy ty1) with
            | .array ty _ => do
              let expr ← transExpr e
              let (posE, tyE) := Tiger.AST.HasInfo.getInfo expr
              match (← actualTy tyE) with
                | .int => pure $ .subscript (pos, ty) lvalue expr
                | _ => throw s!"{posE}: Expected type int, got {tyE}"
            | _ => throw s!"{pos1}: Expected an lvalue of type array, got {ty1}"

  end

end Tiger.Semant
