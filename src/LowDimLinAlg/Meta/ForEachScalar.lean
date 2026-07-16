module

public meta import Lean.Elab.Command

public meta section

namespace LowDimLinAlg.Meta

structure Context where
  scalarTypeName : Lean.Name
  scalarPrefix : String

def Context.scalarType (cx : Context) : Lean.Ident :=
  Lean.mkIdent cx.scalarTypeName

def Context.structure (cx : Context) (suffix : String) : Lean.Ident :=
  Lean.mkIdent <| Lean.Name.mkSimple <| cx.scalarPrefix ++ suffix

def Context.scalarExtNamespace (cx : Context) : Lean.Ident :=
  Lean.mkIdent <| Lean.Name.mkSimple cx.scalarPrefix

def Context.scalarExtMember (cx : Context) (fn : String) : Lean.Ident :=
  Lean.mkIdent <| Lean.Name.mkStr2 cx.scalarPrefix fn

def Context.scalarMember (cx : Context) (fn : String) : Lean.Ident :=
  Lean.mkIdent <| cx.scalarTypeName.str fn

def Context.structureMember (cx : Context) (suffix : String) (fn : String) : Lean.Ident :=
  Lean.mkIdent <| Lean.Name.mkStr2 (cx.scalarPrefix ++ suffix) fn

def signedIntegers := #[
  (``Int8, "I8"),
  (``Int16, "I16"),
  (``Int32, "I32"),
  (``Int64, "I64"),
  (``ISize, "IS"),
]

def unsignedIntegers := #[
  (``UInt8, "U8"),
  (``UInt16, "U16"),
  (``UInt32, "U32"),
  (``UInt64, "U64"),
  (``USize, "US"),
]

def integers := signedIntegers ++ unsignedIntegers

def floats := #[
  (``Float32, "F32"),
  (``Float, "F64"),
]

def signed := floats ++ signedIntegers

def numbers := floats ++ integers

def scalars := numbers.push (``Bool, "B")

def forEachScalar
  (scalars : Array <| Lean.Name × String)
  (f : Context → Lean.Elab.Command.CommandElabM Unit) : Lean.Elab.Command.CommandElabM Unit :=
    scalars.map
      (fun (scalarTypeName, scalarPrefix) => ({ scalarTypeName, scalarPrefix }))
      |>.forM f

def scalarConvertFn? (cxFrom cxTo : Context) : Lean.Elab.Command.CommandElabM (Option Lean.Ident) := do
  let ident := Lean.mkIdent <| cxFrom.scalarTypeName.str <| "to" ++ cxTo.scalarTypeName.toString
  try
    discard <| Lean.resolveGlobalConstNoOverload ident
  catch _ =>
    return none
  return some ident
