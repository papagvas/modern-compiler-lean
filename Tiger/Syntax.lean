import Lean

declare_syntax_cat tiger_decl
declare_syntax_cat tiger_expr
declare_syntax_cat tiger_type

syntax str : tiger_expr
syntax num : tiger_expr
syntax "nil" : tiger_expr
syntax "break" : tiger_expr
syntax ident : tiger_expr
syntax:100 tiger_expr "." ident : tiger_expr
syntax:100 tiger_expr "[" tiger_expr "]" : tiger_expr
syntax:30 tiger_expr " | " tiger_expr:31 : tiger_expr
syntax:40 tiger_expr " & " tiger_expr:41 : tiger_expr
syntax:50 tiger_expr:51 " = " tiger_expr:51 : tiger_expr
syntax:50 tiger_expr:51 " <> " tiger_expr:51 : tiger_expr
syntax:50 tiger_expr:51 " > " tiger_expr:51 : tiger_expr
syntax:50 tiger_expr:51 " >= " tiger_expr:51 : tiger_expr
syntax:50 tiger_expr:51 " < " tiger_expr:51 : tiger_expr
syntax:50 tiger_expr:51 " <= " tiger_expr:51 : tiger_expr
syntax:60 tiger_expr " + " tiger_expr:61 : tiger_expr
syntax:60 tiger_expr " - " tiger_expr:61 : tiger_expr
syntax:70 tiger_expr " * " tiger_expr:71 : tiger_expr
syntax:70 tiger_expr " / " tiger_expr:71 : tiger_expr
syntax:90 "-" tiger_expr : tiger_expr
syntax:20 tiger_expr " := " tiger_expr:20 : tiger_expr
syntax "( " " )" : tiger_expr
syntax "( " tiger_expr ("; " tiger_expr)* " )" : tiger_expr
syntax:10 "if " tiger_expr " then " tiger_expr " else " tiger_expr : tiger_expr
syntax:10 "if " tiger_expr " then " tiger_expr : tiger_expr
syntax:10 "while " tiger_expr " do " tiger_expr : tiger_expr
syntax:10 "for " ident " := " tiger_expr " to " tiger_expr " do " tiger_expr : tiger_expr
syntax:10 "let " tiger_decl+ " in " tiger_expr : tiger_expr
syntax ident "(" tiger_expr,* ")" : tiger_expr
syntax ident "{ " (ident " = " tiger_expr),* " }" : tiger_expr
syntax ident "[" tiger_expr "]" " of " tiger_expr : tiger_expr

syntax:10 "type " ident " = " tiger_type : tiger_decl
syntax:10 "var " ident " := " tiger_expr : tiger_decl
syntax:10 "var " ident " : " ident " := " tiger_expr : tiger_decl
syntax:10 "function " ident "( " (ident " : " ident),* " )" : tiger_decl
syntax:10 "function " ident "( " (ident " : " ident),* " )" ": " ident : tiger_decl

syntax ident : tiger_type
syntax "{ " (ident " : " ident),* " }" : tiger_type
syntax:10 "array" "of" ident : tiger_type
