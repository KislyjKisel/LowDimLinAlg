module

public import LowDimLinAlg.Internal.Dimensionalities

public meta section

namespace LowDimLinAlg.Internal

open Lean

def lit0 := Lean.Syntax.mkNatLit 0
def lit1 := Lean.Syntax.mkNatLit 1

def app (f : Name) : TSyntaxArray `term → TSyntax `term :=
  Syntax.mkApp (mkIdent f)

def foldBinopL {α : Type} (xs : Array α) (op : Lean.Name) (f : α → TSyntax `term) : TSyntax `term :=
  Option.get! <| flip xs.foldl none fun
    | none, x => f x
    | (some s), x => app op #[s, f x]

def foldBinopR {α : Type} (xs : Array α) (op : Lean.Name) (f : α → TSyntax `term) : TSyntax `term :=
  Option.get! <| flip xs.foldr none fun
    | x, none => f x
    | x, (some s) => app op #[f x, s]

def dot (var : Name) (member : String) : Ident :=
  mkIdent <| var.str member

def vget (var : Name) (dim : Dimension) : Ident :=
  dot var dim.str

def lets (var : Ident) (value body : Lean.Term) : Elab.Command.CommandElabM Lean.Term :=
  `(term|let $var:ident := $value:term; $body:term)
