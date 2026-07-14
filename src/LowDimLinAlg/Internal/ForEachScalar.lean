module

public meta import Lean.Elab.Command

public meta section

namespace LowDimLinAlg.Internal

def forEachScalar (f : Lean.Ident → String → Lean.Elab.Command.CommandElabM Unit) : Lean.Elab.Command.CommandElabM Unit :=
  #[
    (``Float32, "F32"),
    (``Float, "F64"),
    (``Int8, "I8"),
    (``Int16, "I16"),
    (``Int32, "I32"),
    (``Int64, "I64"),
    (``UInt8, "U8"),
    (``UInt16, "U16"),
    (``UInt32, "U32"),
    (``UInt64, "U64"),
  ].map (Prod.map Lean.mkIdent id) |>.forM f.uncurry
