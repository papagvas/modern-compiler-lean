import Std.Data.HashMap

open Std

namespace Tiger.Semant.Types

  abbrev Unique := UInt64

  structure SemState where
    currUnique : Unique := 0

  inductive Ty where
    | int    : Int → Ty
    | string : String → Ty
    | nil    : Ty
    | unit   : Ty
    | record : List (String × Ty) → Unique → Ty
    | array  : Ty → Unique → Ty
    | name   : String → Option Ty → Ty
    deriving Repr, BEq

  inductive EnvEntry where
    | varEntry : Ty → EnvEntry
    | funEntry : List Ty → Ty → EnvEntry
    deriving Repr, BEq

  abbrev TEnv := HashMap String Ty
  abbrev VEnv := HashMap String EnvEntry

  abbrev SemantM := ReaderT (TEnv × VEnv) (StateT SemState (Except String)) 

  def getUnique : SemantM UInt64 := modifyGet 
    λ s => (s.currUnique, { s with currUnique := s.currUnique + 1 })

end Tiger.Semant.Types
