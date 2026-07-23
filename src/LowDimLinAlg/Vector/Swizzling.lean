module

public import LowDimLinAlg.Vector.Boolean

import LowDimLinAlg.Internal.Scalars

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

run_cmd
  Internal.scalars.forM fun cx => do
    let v2Ty : Lean.Ident := cx.structure "Vector2"
    let v3Ty : Lean.Ident := cx.structure "Vector3"
    let v4Ty : Lean.Ident := cx.structure "Vector4"
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
          @[inline]
          def $v2swzl2 (v : $v2Ty) : $v2Ty := .mk $v2a $v2b
        )
        Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload v2swzl2)
          s!"Creates a vector with `x := v.{a}, y := v.{b}`"
        for c in axis2 do
          let v2c ← g v2Ty c
          let v2swzl3 := Lean.mkIdent <| v2Ty.getId.append <| .mkSimple (a ++ b ++ c)
          Lean.Elab.Command.elabCommand <| ← `(
            @[inline]
            def $v2swzl3 (v : $v2Ty) : $v3Ty := .mk $v2a $v2b $v2c
          )
          Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload v2swzl3)
            s!"Creates a vector with `x := v.{a}, y := v.{b}, z := v.{c}`"
          for d in axis2 do
            let v2d ← g v2Ty d
            let v2swzl4 := Lean.mkIdent <| v2Ty.getId.append <| .mkSimple (a ++ b ++ c ++ d)
            Lean.Elab.Command.elabCommand <| ← `(
              @[inline]
              def $v2swzl4 (v : $v2Ty) : $v4Ty := .mk $v2a $v2b $v2c $v2d
            )
            Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload v2swzl4)
              s!"Creates a vector with `x := v.{a}, y := v.{b}, z := v.{c}, w := v.{d}`"
    let axis3 := #["x", "y", "z"]
    for a in axis3 do
      let v3a ← g v3Ty a
      for b in axis3 do
        let v3b ← g v3Ty b
        let v3swzl2 := Lean.mkIdent <| v3Ty.getId.append <| .mkSimple (a ++ b)
        Lean.Elab.Command.elabCommand <| ← `(
          @[inline]
          def $v3swzl2 (v : $v3Ty) : $v2Ty := .mk $v3a $v3b
        )
        Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload v3swzl2)
          s!"Creates a vector with `x := v.{a}, y := v.{b}`"
        for c in axis3 do
          let v3c ← g v3Ty c
          let v3swzl3 := Lean.mkIdent <| v3Ty.getId.append <| .mkSimple (a ++ b ++ c)
          Lean.Elab.Command.elabCommand <| ← `(
            @[inline]
            def $v3swzl3 (v : $v3Ty) : $v3Ty := .mk $v3a $v3b $v3c
          )
          Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload v3swzl3)
            s!"Creates a vector with `x := v.{a}, y := v.{b}, z := v.{c}`"
          for d in axis3 do
            let v3d ← g v3Ty d
            let v3swzl4 := Lean.mkIdent <| v3Ty.getId.append <| .mkSimple (a ++ b ++ c ++ d)
            Lean.Elab.Command.elabCommand <| ← `(
              @[inline]
              def $v3swzl4 (v : $v3Ty) : $v4Ty := .mk $v3a $v3b $v3c $v3d
            )
            Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload v3swzl4)
              s!"Creates a vector with `x := v.{a}, y := v.{b}, z := v.{c}, w := v.{d}`"
    let axis4 := #["x", "y", "z", "w"]
    for a in axis4 do
      let v4a ← g v4Ty a
      for b in axis4 do
        let v4b ← g v4Ty b
        let v4swzl2 := Lean.mkIdent <| v4Ty.getId.append <| .mkSimple (a ++ b)
        Lean.Elab.Command.elabCommand <| ← `(
          @[inline]
          def $v4swzl2 (v : $v4Ty) : $v2Ty := .mk $v4a $v4b
        )
        Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload v4swzl2)
          s!"Creates a vector with `x := v.{a}, y := v.{b}`"
        for c in axis4 do
          let v4c ← g v4Ty c
          let v4swzl3 := Lean.mkIdent <| v4Ty.getId.append <| .mkSimple (a ++ b ++ c)
          Lean.Elab.Command.elabCommand <| ← `(
            @[inline]
            def $v4swzl3 (v : $v4Ty) : $v3Ty := .mk $v4a $v4b $v4c
          )
          Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload v4swzl3)
            s!"Creates a vector with `x := v.{a}, y := v.{b}, z := v.{c}`"
          for d in axis4 do
            let v4d ← g v4Ty d
            let v4swzl4 := Lean.mkIdent <| v4Ty.getId.append <| .mkSimple (a ++ b ++ c ++ d)
            Lean.Elab.Command.elabCommand <| ← `(
              @[inline]
              def $v4swzl4 (v : $v4Ty) : $v4Ty := .mk $v4a $v4b $v4c $v4d
            )
            Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload v4swzl4)
              s!"Creates a vector with `x := v.{a}, y := v.{b}, z := v.{c}, w := v.{d}`"
