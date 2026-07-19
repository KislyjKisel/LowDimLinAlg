module

public meta import Lean.Elab.Command
public meta import Std.Data.Iterators

public meta section

namespace LowDimLinAlg.Meta

structure Dimension where
  index : Nat
  char : Char
deriving Inhabited

def dimensions : Array Dimension := #[⟨0, 'x'⟩, ⟨1, 'y'⟩, ⟨2, 'z'⟩, ⟨3, 'w'⟩]

def dimensionalities := fun (i j : Nat) =>
  (i...=j) |>.iter.map dimensions.take

def Dimension.str (dim : Dimension) : String :=
  dim.char.toString

def Dimension.name (dim : Dimension) : Lean.Name :=
  .mkSimple dim.char.toString

def Dimension.ident (dim : Dimension) : Lean.Syntax.Ident :=
  Lean.mkIdent dim.name

def Dimension.indexLit (dim : Dimension) : Lean.Syntax.Term :=
  Lean.Syntax.mkNatLit dim.index
