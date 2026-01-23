import Lean
import Tiger.Parser.Syntax
import Tiger.AST
import Tiger.Location

open Lean
open Tiger.Location

namespace Tiger.Parser.Elab

  abbrev ElabM := ReaderT FileMap (Except String)  

  mutual

    partial def elabExpr (stx : TSyntax `tiger_expr) : ElabM (Tiger.AST.Expr .parse) := do
      let fileMap ← read
      let loc := toSrcLoc fileMap stx.raw

      match stx with
        | `(tiger_expr| $s:str) =>
          pure $ Tiger.AST.Expr.strE loc s.getString
        | `(tiger_expr| $n:num) =>
          pure $ Tiger.AST.Expr.intE loc n.getNat
        | `(tiger_expr| nil) =>
          pure $ Tiger.AST.Expr.nil loc
        | `(tiger_expr| break) =>
          pure $ Tiger.AST.Expr.breakE loc
        | `(tiger_expr| $l:tiger_expr | $r:tiger_expr) => do
          let left ← elabExpr l
          let right ← elabExpr r
          pure $ Tiger.AST.Expr.ifThenElse loc left left right
        | `(tiger_expr| $l:tiger_expr & $r:tiger_expr) => do
          let left ← elabExpr l
          let right ← elabExpr r
          pure $ Tiger.AST.Expr.ifThenElse loc left right left
        | `(tiger_expr| $l:tiger_expr = $r:tiger_expr) => do
          let left ← elabExpr l
          let right ← elabExpr r
          pure $ Tiger.AST.Expr.compare loc Tiger.AST.CompOp.eq left right
        | `(tiger_expr| $l:tiger_expr <> $r:tiger_expr) => do
          let left ← elabExpr l
          let right ← elabExpr r
          pure $ Tiger.AST.Expr.compare loc Tiger.AST.CompOp.neq left right 
        | `(tiger_expr| $l:tiger_expr > $r:tiger_expr) => do
          let left ← elabExpr l
          let right ← elabExpr r
          pure $ Tiger.AST.Expr.compare loc Tiger.AST.CompOp.gt left right
        | `(tiger_expr| $l:tiger_expr >= $r:tiger_expr) => do
          let left ← elabExpr l
          let right ← elabExpr r
          pure $ Tiger.AST.Expr.compare loc Tiger.AST.CompOp.gte left right 
        | `(tiger_expr| $l:tiger_expr < $r:tiger_expr) => do
          let left ← elabExpr l
          let right ← elabExpr r
          pure $ Tiger.AST.Expr.compare loc Tiger.AST.CompOp.lt left right
        | `(tiger_expr| $l:tiger_expr <= $r:tiger_expr) => do
          let left ← elabExpr l
          let right ← elabExpr r
          pure $ Tiger.AST.Expr.compare loc Tiger.AST.CompOp.lte left right 
        | `(tiger_expr| $l:tiger_expr + $r:tiger_expr) => do
          let left ← elabExpr l
          let right ← elabExpr r
          pure $ Tiger.AST.Expr.binE loc Tiger.AST.Op.plus left right
        | `(tiger_expr| $l:tiger_expr - $r:tiger_expr) => do
          let left ← elabExpr l
          let right ← elabExpr r
          pure $ Tiger.AST.Expr.binE loc Tiger.AST.Op.minus left right
        | `(tiger_expr| $l:tiger_expr * $r:tiger_expr) => do
          let left ← elabExpr l
          let right ← elabExpr r
          pure $ Tiger.AST.Expr.binE loc Tiger.AST.Op.mult left right
        | `(tiger_expr| $l:tiger_expr / $r:tiger_expr) => do
          let left ← elabExpr l
          let right ← elabExpr r
          pure $ Tiger.AST.Expr.binE loc Tiger.AST.Op.div left right
        | `(tiger_expr| - $e:tiger_expr) =>
          pure $ Tiger.AST.Expr.negate loc (← elabExpr e)
        | `(tiger_expr| $lv:tiger_expr := $e:tiger_expr) => do
          let lvalue' ← elabLValue? lv
          match lvalue' with
            | none => throw s!"{loc}: Expected lvalue"
            | some lvalue => do
              let expr ← elabExpr e
              pure $ Tiger.AST.Expr.assign loc lvalue expr
        | `(tiger_expr| ()) => pure $ Tiger.AST.Expr.seq loc []
        | `(tiger_expr| ( $es:tiger_expr;* )) => do
          let exprs ← es.getElems.mapM (λ expr => elabExpr expr)
          pure $ Tiger.AST.Expr.seq loc exprs.toList
        | `(tiger_expr| if $e1:tiger_expr then $e2:tiger_expr $[ else $e3:tiger_expr ]?) => do
          let expr1 ← elabExpr e1
          let expr2 ← elabExpr e2
          let expr3 ← e3.mapM elabExpr
          pure $ Tiger.AST.Expr.ifThenElse loc expr1 expr2 expr3
        | `(tiger_expr| while $e1:tiger_expr do $e2:tiger_expr) => do
          let expr1 ← elabExpr e1
          let expr2 ← elabExpr e2
          pure $ Tiger.AST.Expr.whileE loc expr1 expr2
        | `(tiger_expr| for $i:ident := $e1:tiger_expr to $e2:tiger_expr do $e3:tiger_expr) => do
          let expr1 ← elabExpr e1
          let expr2 ← elabExpr e2
          let expr3 ← elabExpr e3
          pure $ Tiger.AST.Expr.forE loc (Tiger.AST.Ident.mkVar i.getId.toString) expr1 expr2 expr3
        | `(tiger_expr| let $ds:tiger_decl* in $e:tiger_expr) => do
          let decls ← ds.mapM (λ decl => elabDecl decl)
          let expr ← elabExpr e
          pure $ Tiger.AST.Expr.letE loc decls.toList expr
        | `(tiger_expr| $i:ident ($es:tiger_expr,*)) => do
          let exprs ← es.getElems.mapM (λ expr => elabExpr expr)
          pure $ Tiger.AST.Expr.funCall loc (Tiger.AST.Ident.mkFunc i.getId.toString) exprs.toList
        | `(tiger_expr| $i:ident { $[ $is:ident = $es:tiger_expr ],* }) => do
          let fields ← (is.zip es).toList.mapM (λ (name', expr') => do
            let expr ← elabExpr expr'
            let name := Tiger.AST.Ident.mkField name'.getId.toString
            pure { name := name, field := expr } )
          pure $ Tiger.AST.Expr.record loc (Tiger.AST.Ident.mkType i.getId.toString) fields 
        | `(tiger_expr| $i:ident [ $e1:tiger_expr ] of $e2:tiger_expr) => do
          let e1 ← elabExpr e1
          let e2 ← elabExpr e2
          pure $ Tiger.AST.Expr.arrayE loc (Tiger.AST.Ident.mkType i.getId.toString) e1 e2
        | _ => do
          let lv' ← elabLValue? stx
          match lv' with
            | none => throw s!"{loc}: Expected expression"
            | some lv => pure $ Tiger.AST.Expr.lvalueE loc lv

    partial def elabLValue? (stx : TSyntax `tiger_expr) : ElabM (Option (Tiger.AST.LValue .parse)) := do
      let fileMap ← read
      let loc := toSrcLoc fileMap stx.raw

      match stx with
        | `(tiger_expr| $i:ident) => pure ∘ some $ Tiger.AST.LValue.var loc (Tiger.AST.Ident.mkVar i.getId.toString)
        | `(tiger_expr| $lv:tiger_expr . $i:ident) => do
          match ( ← elabLValue? lv) with
            | none => throw s!"{loc}: Expected an lvalue"
            | some lvalue => pure ∘ some $ Tiger.AST.LValue.field loc lvalue (Tiger.AST.Ident.mkField i.getId.toString)
        | `(tiger_expr| $lv:tiger_expr [ $e:tiger_expr ]) => do
          let expr ← elabExpr e
          match ( ← elabLValue? lv) with
            | none => throw s!"{loc}: Expected an lvalue"
            | some lvalue => pure ∘ some $ Tiger.AST.LValue.subscript loc lvalue expr
        | _ => pure none
    
    partial def elabDecl (stx : TSyntax `tiger_decl) : ElabM (Tiger.AST.Decl .parse) := do
      let fileMap ← read
      let loc := toSrcLoc fileMap stx.raw

      match stx with
        | `(tiger_decl| type $i:ident = $t:tiger_type) => do
          let ty ← elabKind t
          pure $ Tiger.AST.Decl.typeDecl loc (Tiger.AST.Ident.mkType i.getId.toString) ty
        | `(tiger_decl| var $i:ident $[ : $t:ident ]? := $e:tiger_expr) => do
          let expr ← elabExpr e
          pure $ Tiger.AST.Decl.varDecl loc (Tiger.AST.Ident.mkVar i.getId.toString) (t.map (λ ty => Tiger.AST.Ident.mkType ty.getId.toString)) expr
        | `(tiger_decl| function $i:ident($[ $fs:ident : $ts:ident ],*) $[ : $rt:ident ]? = $e:tiger_expr) => do
          let fname := Tiger.AST.Ident.mkFunc i.getId.toString
          let rtName := rt.map (λ r => Tiger.AST.Ident.mkType r.getId.toString)
          let fields := (fs.zip ts).toList.map (λ (f, t) =>
            let name := Tiger.AST.Ident.mkField f.getId.toString
            let field := Tiger.AST.Ident.mkType t.getId.toString
            { name := name, field := field })
          let expr ← elabExpr e
          pure $ Tiger.AST.Decl.funcDecl loc fname fields rtName expr
        | _ => throw s!"{loc}: Expected a declaration"
    
    partial def elabKind (stx : TSyntax `tiger_type) : ElabM (Tiger.AST.Kind .parse) := do
      let fileMap ← read
      let loc := toSrcLoc fileMap stx.raw

      match stx with
        | `(tiger_type| $i:ident) => pure $ Tiger.AST.Kind.typeId loc (Tiger.AST.Ident.mkType i.getId.toString) 
        | `(tiger_type| { $[ $fs:ident : $ts:ident ],* }) => 
          let fields := (fs.zip ts).toList.map (λ (f, t) =>
            let name := Tiger.AST.Ident.mkField f.getId.toString
            let ty   := Tiger.AST.Ident.mkType t.getId.toString
            { name := name, field := ty })
          pure $ Tiger.AST.Kind.typeMap loc fields
        | `(tiger_type| array of $i:ident) => pure $ Tiger.AST.Kind.arrayType loc (Tiger.AST.Ident.mkType i.getId.toString)
        | _ => throw s!"{loc}: Expected a type"
  end

end Tiger.Parser.Elab
