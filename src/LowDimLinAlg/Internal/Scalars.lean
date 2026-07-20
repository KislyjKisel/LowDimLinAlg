module

public meta import Lean.Elab.Command

public meta section

namespace LowDimLinAlg.Internal

inductive ScalarKind where
| unsignedInteger
| signedInteger
| float
| boolean
deriving BEq

structure ScalarContext where
  scalarTypeName : Lean.Name
  scalarPrefix : String
  scalarKind : ScalarKind

def ScalarContext.scalarType (cx : ScalarContext) : Lean.Ident :=
  Lean.mkIdent cx.scalarTypeName

def ScalarContext.structure (cx : ScalarContext) (suffix : String) : Lean.Ident :=
  Lean.mkIdent <| Lean.Name.mkSimple <| cx.scalarPrefix ++ suffix

def ScalarContext.scalarExtNamespace (cx : ScalarContext) : Lean.Ident :=
  Lean.mkIdent <| Lean.Name.mkSimple cx.scalarPrefix

def ScalarContext.scalarExtMember (cx : ScalarContext) (fn : String) : Lean.Ident :=
  Lean.mkIdent <| Lean.Name.mkStr2 cx.scalarPrefix fn

def ScalarContext.scalarMember (cx : ScalarContext) (fn : String) : Lean.Ident :=
  Lean.mkIdent <| cx.scalarTypeName.str fn

def ScalarContext.structureMember (cx : ScalarContext) (suffix : String) (fn : String) : Lean.Ident :=
  Lean.mkIdent <| Lean.Name.mkStr2 (cx.scalarPrefix ++ suffix) fn

def ScalarContext.isUnsignedInteger (cx : ScalarContext) : Bool :=
  cx.scalarKind == .unsignedInteger

def ScalarContext.isSignedInteger (cx : ScalarContext) : Bool :=
  cx.scalarKind == .signedInteger

def ScalarContext.isFloat (cx : ScalarContext) : Bool :=
  cx.scalarKind == .float

def ScalarContext.isBoolean (cx : ScalarContext) : Bool :=
  cx.scalarKind == .boolean

def ScalarContext.isInteger (cx : ScalarContext) : Bool :=
  cx.isSignedInteger || cx.isUnsignedInteger

def ScalarContext.isNumber (cx : ScalarContext) : Bool :=
  cx.isInteger || cx.isFloat

def ScalarContext.isSigned (cx : ScalarContext) : Bool :=
  cx.isSignedInteger || cx.isFloat

def scalars : Array ScalarContext := #[
  ⟨``Bool, "B", .boolean⟩,
  ⟨``Float32, "F32", .float⟩,
  ⟨``Float, "F64", .float⟩,
  ⟨``UInt8, "U8", .unsignedInteger⟩,
  ⟨``UInt16, "U16", .unsignedInteger⟩,
  ⟨``UInt32, "U32", .unsignedInteger⟩,
  ⟨``UInt64, "U64", .unsignedInteger⟩,
  ⟨``USize, "US", .unsignedInteger⟩,
  ⟨``Int8, "I8", .signedInteger⟩,
  ⟨``Int16, "I16", .signedInteger⟩,
  ⟨``Int32, "I32", .signedInteger⟩,
  ⟨``Int64, "I64", .signedInteger⟩,
  ⟨``ISize, "IS", .signedInteger⟩,
]

def scalarConvertFn? (cxFrom cxTo : ScalarContext) : Lean.Elab.Command.CommandElabM (Option Lean.Ident) := do
  let ident := Lean.mkIdent <| cxFrom.scalarTypeName.str <| "to" ++ cxTo.scalarTypeName.toString
  try
    discard <| Lean.resolveGlobalConstNoOverload ident
  catch _ =>
    return none
  return some ident
