import Tiger.Location
import Tiger.Semant.Types

open Tiger.Location

namespace Tiger.AST

  inductive Tag where
    | var   : Tag
    | type  : Tag
    | func  : Tag
    | field : Tag
    deriving Repr, BEq

  instance : ToString Tag where
    toString tag := match tag with
      | .var => "variable"
      | .type => "type"
      | .func => "function"
      | .field => "field"

  inductive Phase where
    | parse  : Phase
    | semant : Phase
    deriving Repr

-- syntactic construct (not sure what name to go with)
  inductive SynCon where
    | expr   : SynCon
    | decl   : SynCon
    | lvalue : SynCon
    | kind   : SynCon
    deriving Repr

  def Ext (s : SynCon) (p : Phase) : Type := match s, p with
    | _, .parse => SrcLoc
    | .decl, .semant | .kind, .semant => SrcLoc
    | .expr, .semant | .lvalue, .semant => SrcLoc × Tiger.Semant.Types.Ty 

  structure Ident (a : Tag) where
    private mk ::
    name : String
    deriving Repr, BEq

  instance : ToString (Ident a) where
    toString ident := s!"{a} {ident.name}"

  namespace Ident

    def mkVar (str : String) : Ident Tag.var := Ident.mk str
    def mkType (str : String) : Ident Tag.type := Ident.mk str
    def mkFunc (str : String) : Ident Tag.func := Ident.mk str
    def mkField (str : String) : Ident Tag.field := Ident.mk str

  end Ident

  structure Field (a : Type) where
    name  : Ident Tag.field
    field : a

  inductive Kind (p : Phase) where
    | typeId    : Ext .kind p → Ident Tag.type → Kind p
    | typeMap   : Ext .kind p → List (Field (Ident Tag.type)) → Kind p
    | arrayType : Ext .kind p → Ident Tag.type → Kind p

  inductive Op where
    | plus  : Op
    | minus : Op 
    | mult  : Op 
    | div   : Op 

  inductive CompOp where
    | eq    : CompOp
    | lt    : CompOp
    | lte   : CompOp
    | gt    : CompOp
    | gte   : CompOp
    | neq   : CompOp

  class HasInfo (A : (p : Phase) → Type) (s : outParam SynCon) where
    getInfo {s} : A p → Ext s p 

  mutual

    structure TypeDecl (p : Phase) where
      info : Ext .decl p
      name : Ident .type
      ty   : Kind p

    structure FuncDecl (p : Phase) where
      info : Ext .decl p
      name : Ident .func
      args : List (Field (Ident .type))
      rty  : Option (Ident .type)
      body : Expr p

    structure VarDecl (p : Phase) where
      info  : Ext .decl p
      name  : Ident .var
      ty    : Option (Ident .type)
      value : Expr p

    inductive Decls (p : Phase) where
      | funcDecls : List (FuncDecl p) → Decls p
      | typeDecls : List (TypeDecl p) → Decls p
      | varDecls  : List (VarDecl p) → Decls p

    inductive Expr (p : Phase) where
      | nil        : Ext .expr p → Expr p
      | breakE     : Ext .expr p → Expr p
      | intE       : Ext .expr p → Int → Expr p
      | strE       : Ext .expr p → String → Expr p
      | lvalueE    : Ext .expr p → LValue p → Expr p
      | binE       : Ext .expr p → Op → Expr p → Expr p → Expr p
      | compare    : Ext .expr p → CompOp → Expr p → Expr p → Expr p
      | negate     : Ext .expr p → Expr p → Expr p
      | assign     : Ext .expr p → LValue p → Expr p → Expr p
      | seq        : Ext .expr p → List (Expr p) → Expr p
      | ifThenElse : Ext .expr p → Expr p → Expr p → Option (Expr p) → Expr p
      | whileE     : Ext .expr p → Expr p → Expr p → Expr p
      | forE       : Ext .expr p → Ident Tag.var → Expr p → Expr p → Expr p → Expr p
      | letE       : Ext .expr p → List (Decls p) → Expr p → Expr p
      | funCall    : Ext .expr p → Ident Tag.func → List (Expr p) → Expr p
      | record     : Ext .expr p → Ident Tag.type → List (Field (Expr p)) → Expr p
      | arrayE     : Ext .expr p → Ident Tag.type → Expr p → Expr p → Expr p

    inductive LValue (p : Phase) where
      | var       : Ext .lvalue p → Ident Tag.var → LValue p
      | field     : Ext .lvalue p → LValue p → Ident Tag.field → LValue p
      | subscript : Ext .lvalue p → LValue p → Expr p → LValue p

  end

  instance : HasInfo FuncDecl .decl where
    getInfo fdecl := fdecl.info

  instance : HasInfo TypeDecl .decl where
    getInfo tdecl := tdecl.info

  instance : HasInfo VarDecl .decl where
    getInfo vdecl := vdecl.info
  
  instance : HasInfo Expr .expr where
    getInfo expr := match expr with
      | .nil        info => info
      | .breakE     info => info
      | .intE       info  _ => info
      | .strE       info  _ => info
      | .lvalueE    info  _ => info
      | .binE       info  _  _  _ => info
      | .compare    info  _  _  _ => info
      | .negate     info  _ => info
      | .assign     info  _  _ => info
      | .seq        info  _ => info
      | .ifThenElse info  _  _  _ => info
      | .whileE     info  _  _ => info
      | .forE       info  _  _  _  _ => info
      | .letE       info  _  _ => info
      | .funCall    info  _  _ => info
      | .record     info  _  _ => info
      | .arrayE     info  _  _  _ => info

  instance : HasInfo LValue .lvalue where
    getInfo lv := match lv with
      | .var       info _ => info
      | .field     info _ _ => info
      | .subscript info _ _ => info
 
end Tiger.AST
