# Implementation of a Tiger compiler in Lean

## Overview of a Design

This repo tries to closely follow the book, but still takes a few liberties.

1. AST design is slightly different:
    1. I have decided to use phantom types to encode different kinds of identifiers
    2. Since Lean has dependent types I have decided to use simplified Trees that Grow approach
2. The lexing and parsing is also different: 
    1. I have decided to use Lean's metaprogramming facilities to implement parsing phase of the compiler

## Completed Parts of the Compiler

- [x] Parsing
- [x] Type checking
- [ ] Activation records
- [ ] IR Lowering
- [ ] Canonicalization
- [ ] Instruction Selection

## Structure of the Repo
```
├── Main.lean
├── README.md
├── Tiger
│   ├── AST.lean 
│   ├── Basic.lean 
│   ├── Location.lean -- SrcLoc type for tracking source locations
│   ├── Parser
│   │   ├── Elab.lean -- Parsing
│   │   └── Syntax.lean -- Syntax declarations
│   ├── Semant
│   │   └── Types.lean -- Tiger's type info
│   └── Semant.lean -- Typechecker
├── Tiger.lean
├── lake-manifest.json
├── lakefile.toml
└── lean-toolchain
```
