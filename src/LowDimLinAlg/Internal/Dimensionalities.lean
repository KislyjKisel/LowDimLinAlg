module

public meta import Lean.Elab.Command
public meta import Std.Data.Iterators

public meta section

namespace LowDimLinAlg.Internal

structure Dimension where
  index : Nat
  char : Char
deriving Inhabited

def Dimension.x : Dimension := ⟨0, 'x'⟩
def Dimension.y : Dimension := ⟨1, 'y'⟩
def Dimension.z : Dimension := ⟨2, 'z'⟩
def Dimension.w : Dimension := ⟨3, 'w'⟩

def dimensionalities : Array (Array Dimension) := #[
  #[.x, .y],
  #[.x, .y, .z],
  #[.x, .y, .z, .w],
]

def Dimension.str (dim : Dimension) : String :=
  dim.char.toString

def Dimension.name (dim : Dimension) : Lean.Name :=
  .mkSimple dim.char.toString

def Dimension.ident (dim : Dimension) : Lean.Syntax.Ident :=
  Lean.mkIdent dim.name

def Dimension.indexLit (dim : Dimension) : Lean.Syntax.Term :=
  Lean.Syntax.mkNatLit dim.index
