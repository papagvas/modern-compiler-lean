inductive Tag where
  | var   : Tag
  | type  : Tag
  | func  : Tag
  | field : Tag

structure Ident (a : Tag) where
  private mk ::
  name : String

namespace Ident

  def mkVar (str : String) : Ident Tag.var     := Ident.mk str
  def mkType (str : String) : Ident Tag.type   := Ident.mk str
  def mkFunc (str : String) : Ident Tag.func   := Ident.mk str
  def mkField (str : String) : Ident Tag.field := Ident.mk str

end Ident

structure Field (a : Type) where
  name  : Ident Tag.field
  field : a

inductive Kind where
  | typeId    : Ident Tag.type → Kind
  | typeMap   : List (Field (Ident Tag.type)) → Kind
  | arrayType : Ident Tag.type → Kind

inductive Op where
  | plus  : Op
  | minus : Op 
  | mult  : Op 
  | div   : Op 
  | eq    : Op
  | lt    : Op
  | lte   : Op
  | gt    : Op
  | gte   : Op
  | neq   : Op

mutual
  inductive Decl where
    | typeDecl : Ident Tag.type → Kind → Decl
    | varDecl  : Ident Tag.var → Option (Ident Tag.type) → Expr → Decl
    | funcDecl : Ident Tag.func → List (Field (Ident Tag.type)) → Option (Ident Tag.type) → Expr → Decl

  inductive Expr where
    | nil : Expr
    | breakE : Expr
    | intE : Int → Expr
    | strE : String → Expr
    | lvalueE : LValue → Expr
    | binE : Op → Expr → Expr → Expr
    | negate : Expr → Expr
    | assign : LValue → Expr → Expr
    | seq : List Expr → Expr
    | ifThenElse : Expr → Expr → Option Expr → Expr
    | whileE : Expr → Expr → Expr
    | forE : Ident Tag.var → Expr → Expr → Expr → Expr
    | letE : List Decl → Expr → Expr
    | funCall : Ident Tag.func → List Expr → Expr
    | record : Ident Tag.type → List (Field Expr) → Expr
    | arrayE : Ident Tag.type → Expr → Expr → Expr

  inductive LValue where
    | var       : Ident Tag.var → LValue
    | field     : LValue → Ident Tag.field → LValue
    | subscript : LValue → Expr → LValue 
end
