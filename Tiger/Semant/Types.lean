import Std.Data.HashMap

open Std

namespace Tiger.Semant.Types

  abbrev Unique := UInt64

  structure SemState where
    currUnique : Unique := 0

  inductive Ty where
    | int    : Ty
    | string : Ty
    | nil    : Ty
    | unit   : Ty
    | record : List (String × Ty) → Unique → Ty
    | array  : Ty → Unique → Ty
    | name   : String → Option Ty → Ty
    deriving Repr, BEq

  def tyToString (ty : Ty) : String := match ty with
    | .int => "int" 
    | .string => "string"
    | .nil => "nil"
    | .unit => "unit"
    | .record _ i => s!"record #{i}"
    | .array t i => 
      s!"array of {tyToString t} #{i}" 
    | .name n _ => n

  instance : ToString Ty where
    toString := tyToString

  inductive ReadOnly where
    | readOnly : ReadOnly
    deriving Repr, BEq

  inductive EnvEntry where
    | varEntry : Ty → Option ReadOnly → EnvEntry
    | funEntry : List Ty → Ty → EnvEntry
    deriving Repr, BEq

  abbrev TEnv := HashMap String Ty
  abbrev VEnv := HashMap String EnvEntry

  inductive Loop? where
    | loop   : Loop?
    | noLoop : Loop?

  structure Scope where
    tenv  : TEnv
    venv  : VEnv
    loop? : Loop?

  abbrev SemantM := ReaderT Scope (StateT SemState (Except String)) 

  def getUnique : SemantM UInt64 := modifyGet 
    λ s => (s.currUnique, { s with currUnique := s.currUnique + 1 })

end Tiger.Semant.Types
