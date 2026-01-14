import Lean

declare_syntax_cat tiger_decl
declare_syntax_cat tiger_expr
declare_syntax_cat tiger_type

syntax str : tiger_expr
syntax num : tiger_expr
syntax "nil" : tiger_expr
syntax "break" : tiger_expr
syntax ident : tiger_expr
syntax tiger_expr "." ident : tiger_expr
syntax tiger_expr "[" tiger_expr "]" : tiger_expr
syntax tiger_expr " | " tiger_expr : tiger_expr
syntax tiger_expr " & " tiger_expr : tiger_expr
syntax tiger_expr " = " tiger_expr : tiger_expr
syntax tiger_expr " <> " tiger_expr : tiger_expr
syntax tiger_expr " > " tiger_expr : tiger_expr
syntax tiger_expr " >= " tiger_expr : tiger_expr
syntax tiger_expr " < " tiger_expr : tiger_expr
syntax tiger_expr " <= " tiger_expr : tiger_expr
syntax tiger_expr " + " tiger_expr : tiger_expr
syntax tiger_expr " - " tiger_expr : tiger_expr
syntax tiger_expr " * " tiger_expr : tiger_expr
syntax tiger_expr " / " tiger_expr : tiger_expr
syntax "-" tiger_expr : tiger_expr
syntax tiger_expr " := " tiger_expr : tiger_expr
syntax "( " tiger_expr ("; " tiger_expr)* " )" : tiger_expr
syntax "if " tiger_expr " then " tiger_expr " else " tiger_expr : tiger_expr
syntax "if " tiger_expr " then " tiger_expr : tiger_expr
syntax "while " tiger_expr " do " tiger_expr : tiger_expr
syntax "for " ident " := " tiger_expr " to " tiger_expr " do " tiger_expr : tiger_expr
syntax "let " tiger_decl+ " in " tiger_expr : tiger_expr
syntax ident "(" tiger_expr,* ")" : tiger_expr
syntax ident "{ " (ident " = " tiger_expr),* " }" : tiger_expr
syntax ident "[" tiger_expr "]" " of " tiger_expr : tiger_expr

syntax "type " ident " = " tiger_type : tiger_decl
syntax "var " ident " := " tiger_expr : tiger_decl
syntax "var " ident " : " ident " := " tiger_expr : tiger_decl
syntax "function " ident "( " (ident " : " ident),* " )" : tiger_decl
syntax "function " ident "( " (ident " : " ident),* " )" ": " ident : tiger_decl

syntax ident : tiger_type
syntax "{ " (ident " : " ident ", "),* " }" : tiger_type
syntax "array of " ident : tiger_type
