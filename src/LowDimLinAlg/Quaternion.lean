module

public import LowDimLinAlg.Vector.Numbers

import LowDimLinAlg.Internal.Scalars

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

run_cmd
  Internal.scalars.forM fun cx => do
    if !cx.isFloat then return
    let sTy := cx.scalarType
    let qTy := cx.structure "Quaternion"
    let v3Ty := cx.structure "Vector3"
    let v4Ty := cx.structure "Vector4"
    Lean.Elab.Command.elabCommand <| ← `(
      structure $qTy:ident where
        x : $sTy
        y : $sTy
        z : $sTy
        w : $sTy
      deriving BEq, Repr, Inhabited

      namespace $qTy

      -- /-- All zeros. -/
      -- def zero : $qTy := ⟨0, 0, 0, 0⟩

      -- /-- The identity quaternion. Corresponds to no rotation. -/
      -- def identity : $qTy := ⟨0, 0, 0, 1⟩

      -- /-- Vector componentwise copy. -/
      -- def ofVector4 (v : $v4Ty) : $qTy := { v with }

      end $qTy
    )
