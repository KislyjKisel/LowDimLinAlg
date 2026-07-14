module

import LowDimLinAlg.Internal.ForEachScalar

public section

namespace LowDimLinAlg

set_option hygiene false in
run_cmd
  Internal.forEachScalar fun sTy sPrefix => do
    let v2Ty := Lean.mkIdent <| .mkSimple <| sPrefix ++ "Vector2"
    let v3Ty := Lean.mkIdent <| .mkSimple <| sPrefix ++ "Vector3"
    let v4Ty := Lean.mkIdent <| .mkSimple <| sPrefix ++ "Vector4"
    Lean.Elab.Command.elabCommand <| ← `(
      structure $v2Ty where
        x : $sTy
        y : $sTy
      deriving BEq, Repr, Inhabited

      structure $v3Ty where
        x : $sTy
        y : $sTy
        z : $sTy
      deriving BEq, Repr, Inhabited

      structure $v4Ty where
        x : $sTy
        y : $sTy
        z : $sTy
        w : $sTy
      deriving BEq, Repr, Inhabited
    )
