module

public import LowDimLinAlg.Vector.Constants
public import LowDimLinAlg.Vector.Numbers

import LowDimLinAlg.Internal.Dimensionalities
import LowDimLinAlg.Internal.Scalars
import LowDimLinAlg.Internal.Syntax

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Lean Elab Command
open Internal

run_cmd
  let byGetElemTactic ← `(by get_elem_tactic)
  for dims in dimensionalities 2 4 do
    let structureSuffix := "Vector" ++ toString dims.size
    let dimsSizeLit := Syntax.mkNatLit dims.size
    let f64vTy := mkIdent <| .mkSimple <| "F64" ++ structureSuffix
    let ofF64Arr := mkIdent <| f64vTy.getId.str "ofFloatArray"
    let toF64Arr := mkIdent <| f64vTy.getId.str "toFloatArray"
    elabCommand <| ← `(
      /-- Creates a vector from a scalar array. Panics if the array does not contain enough elements. -/
      @[inline]
      def $ofF64Arr (a : FloatArray) : $f64vTy :=
        if h: a.size >= $dimsSizeLit
          then $(app `mk <| (0...dims.size).iter.map (fun i => app ``getElem #[mkIdent `a, Syntax.mkNatLit i, byGetElemTactic]) |>.toArray)
          else panic! $(Syntax.mkStrLit s!"array contains less than {dims.size} values")

      /-- Pushes vector components to a scalar array. -/
      @[inline]
      def $toF64Arr (v : $f64vTy) (dst : FloatArray := by exact FloatArray.emptyWithCapacity 2) : FloatArray :=
        $(flip dims.foldl (mkIdent `dst) fun r dim => app ``FloatArray.push #[r, vget `v dim])
    )
    scalars.forM fun cx => do
      if !cx.isFloat then return
      let vTy := cx.structure structureSuffix
      let sTy := cx.scalarType
      let sIsFinite := cx.scalarMember "isFinite"
      let sLerp := cx.scalarExtMember "lerp"
      elabCommand <| ← `(
        namespace $vTy

        deriving instance BEq for $vTy

        /--
        Componentwise clamping of components.

        Panics in debug if for any axis `min` > `max`, `min` is NaN, or `max` is NaN.
        -/
        @[inline]
        def clamp (v min max : $vTy) : $vTy :=
          ⟨$(dims.map fun dim => app (cx.scalarExtMember "clamp").getId <| #[`min, `max, `v].map (vget · dim)),*⟩

        /-- Componentwise sign (does not return zeros). -/
        @[inline]
        def sign (v : $vTy) : $vTy :=
          ⟨$(dims.map fun dim => app (cx.scalarExtMember "sign").getId #[vget `v dim]),*⟩

        /-- Vector length. -/
        @[inline]
        def length (v : $vTy) : $sTy :=
          $(cx.scalarMember "sqrt") <| lengthSqr v

        /-- Distance between two points represented by vectors from any third point. -/
        @[inline]
        def distance (a b : $vTy) : $sTy :=
          length (a - b)

        /--
        Normalizes vector to the length of `1`.

        Returns `none` if the resulting vector is not finite.
        -/
        @[inline]
        def normalize? (v : $vTy) : Option $vTy :=
          let v' := v * (1 / v.length)
          if v'.any <| not ∘ $sIsFinite
            then none
            else some v'

        /--
        Normalizes vector to the length of `1`.

        Panics in debug if any component of `v/|v|` is not finite.
        -/
        @[inline]
        def normalize (v : $vTy) : $vTy :=
          let v' := v * (1 / v.length)
          debug_assert! v'.any <| not ∘ $sIsFinite
          v'

        /-- Checks whether the length of `v` is 1. -/
        @[inline]
        def isNormalized (maxSqrDelta : $sTy := 2e-4) (v : $vTy) : Bool :=
          $(cx.scalarMember "abs") (v.lengthSqr - 1) <= maxSqrDelta

        /--
        Projection of `a` onto `b`.

        Panics in debug if `1/|b|²` is not finite.
        -/
        @[inline]
        def projectOnto (a b : $vTy) : $vTy :=
          let invBSqrLen := 1 / b.lengthSqr
          debug_assert! $sIsFinite invBSqrLen
          b * (dot a b) * invBSqrLen

        /--
        Projection of `a` onto `b`.

        Panics in debug if `b` is not normalized.
        -/
        @[inline]
        def projectOntoNormalized (a b : $vTy) : $vTy :=
          debug_assert! b.isNormalized
          b * (dot a b)

        /--
        Rejection of `a` from `b`.

        Rejection is the part of `a` that is missing from its projection
        (`a = rejection + projection`).

        Panics in debug if `1/|b|²` is not finite.
        -/
        @[inline]
        def rejectFrom (a b : $vTy) : $vTy :=
          a - projectOnto a b

        /--
        Rejection of `a` from `b`.

        Rejection is the part of `a` that is missing from its projection
        (`a = rejection + projection`).

        Panics in debug if `b` is not normalized.
        -/
        @[inline]
        def rejectFromNormalized (a b : $vTy) : $vTy :=
          a - projectOntoNormalized a b

        /--
        Performs a linear interpolation between `start` and `end` based on `t`.

        When `t` is `0`, the result will be `start`.
        When `t` is `1`, the result will be `end`.
        When `t` is outside of the range, the result is linearly extrapolated.

        Returns `NaN` if `t`, `start` or `end` is NaN (for each axis).
        -/
        @[inline]
        def lerp (start «end» : $vTy) (t : $sTy) : $vTy :=
          start + t * («end» - start)

        /--
        Reflect `v` across a line with a `normal`.

        Panics in debug if `normal` is not normalized.
        -/
        @[inline]
        def reflectAlongNormal (v normal : $vTy) : $vTy :=
          debug_assert! normal.isNormalized
          v - (2 * dot v normal) * normal

        /--
        Reflect `v` across a line with a perpendicular `perp`.

        Panics in debug if `2/|perp|²` is not finite.
        -/
        @[inline]
        def reflectAlong (v perp : $vTy) : $vTy :=
          let k := 2 / perp.lengthSqr
          debug_assert! $sIsFinite k
          v - k * dot v perp * perp

        /--
        Reflect `v` across a line with a `normal`.

        Assumes `normal` is normalized.
        -/
        @[inline]
        def reflectAlong' (v normal : $vTy) : $vTy :=
          v - (2 * dot v normal) * normal

        /--
        Reflect `v` across a `line`.

        Panics in debug if `line` is not normalized.
        -/
        @[inline]
        def reflectAcrossNormal (v line : $vTy) : $vTy :=
          debug_assert! line.isNormalized
          2 * dot v line * line - v

        /--
        Reflect `v` across a `line`.

        Panics in debug if `2/|line|²` is not finite.
        -/
        @[inline]
        def reflectAcross (v line : $vTy) : $vTy :=
          let k := 2 / line.lengthSqr
          debug_assert! $sIsFinite k
          k * dot v line * line - v

        /--
        Reflect `v` across a `line`.

        Assumes `line` is normalized.
        -/
        @[inline]
        def reflectAcross' (v line : $vTy) : $vTy :=
          2 * dot v line * line - v

        /--
        Move `v` towards `target`.

        Panics in debug if `maxDistance` is negative.
        -/
        @[inline]
        def moveTowards (v target : $vTy) (maxDistance : $sTy) : $vTy :=
          debug_assert! maxDistance >= 0
          let delta := target - v
          let distanceSqr := delta.lengthSqr
          if distanceSqr <= maxDistance * maxDistance
            then target
            else v + delta * (maxDistance / distanceSqr.sqrt)

        /--
        Compute the direction of a refracted ray where
        * `v`: direction of the incoming ray
        * `n`: normal vector of the interface of two optical media
        * `r`: the ratio of the refractive index of the medium from where the ray comes
          to the refractive index of the medium on the other side of the surface

        Panics in debug if either `v` or `n` is not normalized.
        -/
        @[inline]
        def refract (v n : $vTy) (r : $sTy) : $vTy :=
          debug_assert! n.isNormalized && v.isNormalized
          let «v∙n» := dot v n
          let d := 1 - r * r * (1 - «v∙n» * «v∙n»)
          if d >= 0
            then (v * r) - (n * (r * «v∙n» + d.sqrt))
            else .zero

        /--
        Checks whether absolute difference between corresponding
        component values is less than or equal to `maxDifference`.
        -/
        @[inline]
        def almostEqual (a b : $vTy) (maxDifference : $sTy) : Bool :=
          (a - b).all <| (· <= maxDifference) ∘ $(cx.scalarMember "abs")

        /--
        Changes the vector's length to be between `min` and `max`.

        Panics in debug if either `min` or `max` is negative, or if `min > max`.
        -/
        @[inline]
        def clampLength (min max : $sTy) (v : $vTy) : $vTy :=
          debug_assert! min >= 0 && max >= 0 && min <= max
          let lenSqr := lengthSqr v
          if lenSqr < min * min then
            v * (min / lenSqr.sqrt)
          else if lenSqr > max * max then
            v * (max / lenSqr.sqrt)
          else
            v

        /--
        Changes the vector's length to be not less than `min`.

        Panics in debug if `min` is negative.
        -/
        @[inline]
        def clampLengthMin (min : $sTy) (v : $vTy) : $vTy :=
          debug_assert! min >= 0
          let lenSqr := lengthSqr v
          if lenSqr < min * min
            then v * (min / lenSqr.sqrt)
            else v

        /--
        Changes the vector's length to be not greater than `max`.

        Panics in debug if `max` is negative.
        -/
        @[inline]
        def clampLengthMax (max : $sTy) (v : $vTy) : $vTy :=
          debug_assert! max >= 0
          let lenSqr := lengthSqr v
          if lenSqr > max * max
            then v * (max / lenSqr.sqrt)
            else v

        /-- Returns a vector with the direction of `v` and length `s`. -/
        @[inline]
        def resize (s : $sTy) (v : $vTy) : $vTy :=
          v * (s / v.length)

        /-- Returns a vector with the direction of `v` and length of `target`. -/
        @[inline]
        def resizeAs (v target : $vTy) : $vTy :=
          v * (target.lengthSqr / v.lengthSqr).sqrt
      )
      if dims.size = 2 then
        elabCommand <| ← `(
          /--
          Creates a unit vector from `angle`.

          Angle is counterclockwise if Y is up and X is down.
          -/
          @[inline]
          def fromAngle (angle : $sTy) : $vTy :=
            ⟨angle.cos, angle.sin⟩

          /--
          Creates a vector from `length` and `angle`.

          Angle is counterclockwise if Y is up and X is down.
          -/
          @[inline]
          def fromLengthAngle (length angle : $sTy) : $vTy :=
            length * fromAngle angle

          /--
          Returns angle between positive X axis and the ray defined by vector `v` and origin `(0, 0)`.

          Panics in debug if the length of `v` is zero.
          -/
          @[inline]
          def angle (v : $vTy) : $sTy :=
            debug_assert! v.length > 0
            $(cx.scalarMember "atan2") v.y v.x

          /-- Angle between two vectors (counterclockwise if Y is up and X is right). -/
          @[inline]
          def angleBetween (a b : $vTy) : $sTy :=
            $(cx.scalarMember "atan2") (cross a b) (dot a b)

          /-- Angle between positive X axis and a line from point `a` to `b`. -/
          @[inline]
          def lineAngle (a b : $vTy) : $sTy :=
            angle (b - a)

          /-- Rotate `v` by `angle`. -/
          @[inline]
          def rotate (angle : $sTy) (v : $vTy) : $vTy :=
            let cos := angle.cos
            let sin := angle.sin
            ⟨v.x * cos - v.y * sin, v.x * sin + v.y * cos⟩

          /--
          Rotates `v` towards `target` up to `maxRotation` radians.

          Panics in debug if `maxRotation` is negative.
          -/
          @[inline]
          def rotateTowards (v target : $vTy) (maxRotation : $sTy) : $vTy :=
            debug_assert! maxRotation >= 0
            let angle := v.angleBetween target
            let angleAbs := angle.abs
            dbg_trace angleAbs
            if angleAbs <= maxRotation
              then target.resizeAs v
              else v.rotate <| if angle < 0 then -maxRotation else maxRotation
        )
      if dims.size = 3 then
        elabCommand <| ← `(
          /-- Angle between two vectors. -/
          @[inline]
          def angleBetween (a b : $vTy) : $sTy :=
            $(cx.scalarMember "atan2") (cross a b).length (dot a b)

          /--
          Rotates a vector around an axis.
          In a right-handed coordinate system the rotation is clockwise
          when the axis is the view direction.

          Panics in debug if `axis` is not normalized.
          -/
          def rotate (v axis : $vTy) (angle : $sTy) : $vTy :=
            -- From `Raylib` with edits
            debug_assert! axis.isNormalized
            let angle := 0.5 * angle
            let w := angle.sin * axis
            let wv := cross w v
            let wwv := cross w wv
            v + 2 * angle.cos * wv + (2 : $sTy) * wwv

          /--
          Rotates a vector around the X axis.
          In a right-handed coordinate system the rotation is clockwise
          when the axis is the view direction.
          -/
          @[inline]
          def rotateX (v : $vTy) (angle : $sTy) : $vTy :=
            let sin := angle.sin
            let cos := angle.cos
            ⟨v.x, v.y * cos - v.z * sin, v.y * sin + v.z * cos⟩

          /--
          Rotates a vector around the Y axis.
          In a right-handed coordinate system the rotation is clockwise
          when the axis is the view direction.
          -/
          @[inline]
          def rotateY (v : $vTy) (angle : $sTy) : $vTy :=
            let sin := angle.sin
            let cos := angle.cos
            ⟨v.x * cos + v.z * sin, v.y, v.z * cos - v.x * sin⟩

          /--
          Rotates a vector around the Z axis.
          In a right-handed coordinate system the rotation is clockwise
          when the axis is the view direction.
          -/
          @[inline]
          def rotateZ (v : $vTy) (angle : $sTy) : $vTy :=
            let sin := angle.sin
            let cos := angle.cos
            ⟨v.x * cos - v.y * sin, v.x * sin + v.y * cos, v.z⟩

          /--
          Rotates `v` towards `target` up to `maxRotation` radians.

          Panics in debug if `maxRotation` is negative.
          Also panics in debug if the angle between vectors is greater than `maxRotation`
          and their cross product can't be normalized (they are close to collinear).
          -/
          @[inline]
          def rotateTowards (v target : $vTy) (maxRotation : $sTy) : $vTy :=
            debug_assert! maxRotation >= 0
            let angle := v.angleBetween target
            let angleAbs := angle.abs
            dbg_trace angleAbs
            if angleAbs <= maxRotation
              then resizeAs v target
              else v.rotate ((v.cross target).normalize) (if angle < 0 then -maxRotation else maxRotation)

          /--
          Returns some unnormalized vector orthogonal to the argument.

          Assumes that the input vector is finite and non-zero.
          -/
          @[inline]
          def anyOrthogonal (v : $vTy) : $vTy :=
            if v.x.abs > v.y.abs
              then ⟨-v.z, 0, v.x⟩
              else ⟨0, v.z, -v.y⟩

          /--
          Performs a spherical linear interpolation between `start` and `end` based on `t`.

          When `t` is `0`, the result will be `start`.
          When `t` is `1`, the result will be `end`.
          When `t` is outside of the range, the result is linearly extrapolated.

          Returns `NaN` if `value`, `start` or `end` is NaN (for each axis).
          -/
          def slerp (start «end» : $vTy) (t : $sTy) : $vTy :=
            -- From `https://github.com/bitshifter/glam-rs` with edits
            let startLen := start.length
            let endLen := end.length
            let cos := start.dot «end» / (startLen * endLen)
            if cos.abs < 1 - 3e-7 then
              let angle := cos.acos
              let sin := angle.sin
              let t1 := (angle * (1 - t)).sin
              let t2 := (angle * t).sin
              let len := $sLerp startLen endLen t
              (t1 * (len / startLen) * start + t2 * (len / endLen) * «end») / sin
            else if cos < 0.0 then
              ($sLerp startLen endLen t / startLen) * start.rotate start.anyOrthogonal.normalize (t * $(cx.scalarExtMember "pi"))
            else
              start.lerp «end» t
        )
      elabCommand <| ← `(
        end $vTy
      )
