module

public import LowDimLinAlg.Vector.«3»
public import LowDimLinAlg.Vector.«4»

import LowDimLinAlg.Meta.ForEachScalar

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

run_cmd
  Meta.forEachScalar Meta.floats fun cx => do
    let sTy := cx.scalarType
    let qTy := cx.structure "Quaternion"
    let v3Ty := cx.structure "Vector3"
    let v4Ty := cx.structure "Vector4"
    Lean.Elab.Command.elabCommand <| ← `(
      structure $qTy where
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
