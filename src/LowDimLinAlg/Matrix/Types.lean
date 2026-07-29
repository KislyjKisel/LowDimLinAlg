module

public import LowDimLinAlg.Vector.Types

import LowDimLinAlg.Internal.Dimensionalities
import LowDimLinAlg.Internal.Scalars

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Lean Elab Command
open Internal

run_cmd
  scalars.forM fun cx => do
    if !cx.isFloat then return
    let sTy := cx.scalarType
    let m2Ty : Ident := cx.structure "Matrix2"
    let m3Ty : Ident := cx.structure "Matrix3"
    let m4Ty : Ident := cx.structure "Matrix4"
    elabCommand <| ← `(
      structure $m2Ty where
        m11 : $sTy
        m12 : $sTy
        m21 : $sTy
        m22 : $sTy
      deriving BEq, Inhabited, Repr

      structure $m3Ty where
        m11 : $sTy
        m12 : $sTy
        m13 : $sTy
        m21 : $sTy
        m22 : $sTy
        m23 : $sTy
        m31 : $sTy
        m32 : $sTy
        m33 : $sTy
      deriving BEq, Inhabited, Repr

      structure $m4Ty where
        m11 : $sTy
        m12 : $sTy
        m13 : $sTy
        m14 : $sTy
        m21 : $sTy
        m22 : $sTy
        m23 : $sTy
        m24 : $sTy
        m31 : $sTy
        m32 : $sTy
        m33 : $sTy
        m34 : $sTy
        m41 : $sTy
        m42 : $sTy
        m43 : $sTy
        m44 : $sTy
      deriving BEq, Inhabited, Repr
    )
    let dmvs := dimensionalities.iter.zip #[m2Ty, m3Ty, m4Ty].iter
    for (dims, mTy) in dmvs do
      addDocStringCore (← resolveGlobalConstNoOverload mTy) <|
        s!"{dims.size}×{dims.size} {cx.scalarTypeName} matrix.\n\nFields are stored in row-major order."
