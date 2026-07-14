module

public import LowDimLinAlg.Vector

import LowDimLinAlg.Internal.ForEachScalar

public section

namespace LowDimLinAlg

set_option hygiene false in
run_cmd
  Internal.forEachScalar fun _ sPrefix => do
    let v2Ty := Lean.mkIdent <| .mkSimple <| sPrefix ++ "Vector2"
    let v3Ty := Lean.mkIdent <| .mkSimple <| sPrefix ++ "Vector3"
    let v4Ty := Lean.mkIdent <| .mkSimple <| sPrefix ++ "Vector4"
    let g (t : Lean.Ident) (k : String) : Lean.Elab.Command.CommandElabM (Lean.TSyntax `term) :=
      let accessor := Lean.mkIdent <| t.getId.append <| .mkSimple k
      `($accessor v)
    let axis2 := #["x", "y"]
    for a in axis2 do
      let v2a ← g v2Ty a
      for b in axis2 do
        let v2b ← g v2Ty b
        let v2swzl2 := Lean.mkIdent <| v2Ty.getId.append <| .mkSimple (a ++ b)
        Lean.Elab.Command.elabCommand <| ← `(
          abbrev $v2swzl2 (v : $v2Ty) : $v2Ty := ⟨$v2a, $v2b⟩
        )
        for c in axis2 do
          let v2c ← g v2Ty c
          let v2swzl3 := Lean.mkIdent <| v2Ty.getId.append <| .mkSimple (a ++ b ++ c)
          Lean.Elab.Command.elabCommand <| ← `(
            abbrev $v2swzl3 (v : $v2Ty) : $v3Ty := ⟨$v2a, $v2b, $v2c⟩
          )
          for d in axis2 do
            let v2d ← g v2Ty d
            let v2swzl4 := Lean.mkIdent <| v2Ty.getId.append <| .mkSimple (a ++ b ++ c ++ d)
            Lean.Elab.Command.elabCommand <| ← `(
              abbrev $v2swzl4 (v : $v2Ty) : $v4Ty := ⟨$v2a, $v2b, $v2c, $v2d⟩
            )
    let axis3 := #["x", "y", "z"]
    for a in axis3 do
      let v3a ← g v3Ty a
      for b in axis3 do
        let v3b ← g v3Ty b
        let v3swzl2 := Lean.mkIdent <| v3Ty.getId.append <| .mkSimple (a ++ b)
        Lean.Elab.Command.elabCommand <| ← `(
          abbrev $v3swzl2 (v : $v3Ty) : $v2Ty := ⟨$v3a, $v3b⟩
        )
        for c in axis3 do
          let v3c ← g v3Ty c
          let v3swzl3 := Lean.mkIdent <| v3Ty.getId.append <| .mkSimple (a ++ b ++ c)
          Lean.Elab.Command.elabCommand <| ← `(
            abbrev $v3swzl3 (v : $v3Ty) : $v3Ty := ⟨$v3a, $v3b, $v3c⟩
          )
          for d in axis3 do
            let v3d ← g v3Ty d
            let v3swzl4 := Lean.mkIdent <| v3Ty.getId.append <| .mkSimple (a ++ b ++ c ++ d)
            Lean.Elab.Command.elabCommand <| ← `(
              abbrev $v3swzl4 (v : $v3Ty) : $v4Ty := ⟨$v3a, $v3b, $v3c, $v3d⟩
            )
    let axis4 := #["x", "y", "z", "w"]
    for a in axis4 do
      let v4a ← g v4Ty a
      for b in axis4 do
        let v4b ← g v4Ty b
        let v4swzl2 := Lean.mkIdent <| v4Ty.getId.append <| .mkSimple (a ++ b)
        Lean.Elab.Command.elabCommand <| ← `(
          abbrev $v4swzl2 (v : $v4Ty) : $v2Ty := ⟨$v4a, $v4b⟩
        )
        for c in axis4 do
          let v4c ← g v4Ty c
          let v4swzl3 := Lean.mkIdent <| v4Ty.getId.append <| .mkSimple (a ++ b ++ c)
          Lean.Elab.Command.elabCommand <| ← `(
            abbrev $v4swzl3 (v : $v4Ty) : $v3Ty := ⟨$v4a, $v4b, $v4c⟩
          )
          for d in axis4 do
            let v4d ← g v4Ty d
            let v4swzl4 := Lean.mkIdent <| v4Ty.getId.append <| .mkSimple (a ++ b ++ c ++ d)
            Lean.Elab.Command.elabCommand <| ← `(
              abbrev $v4swzl4 (v : $v4Ty) : $v4Ty := ⟨$v4a, $v4b, $v4c, $v4d⟩
            )
