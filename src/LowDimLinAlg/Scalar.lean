module

import LowDimLinAlg.Internal.Scalars

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

run_cmd
  Internal.scalars.forM fun cx => do
    if !cx.isFloat then return
    let sTy := cx.scalarType
    Lean.Elab.Command.elabCommand <| ← `(
      namespace $cx.scalarExtNamespace
      /--
      Restricts a value to a certain interval.
      Returns NaN if `value` is NaN, `min` if `value` < `min`, `max` if `value` > `max` and `value` otherwise.

      Panics in debug if `min` > `max`, `min` is NaN, or `max` is NaN.
      -/
      @[inline]
      def clamp (min max value : $sTy) : $sTy :=
        debug_assert! !min.isNaN && !max.isNaN && min <= max
        if value.isNaN
          then value
          else Max.max min (Min.min value max)

      /--
      Restricts a value to an interval centered around zero.
      Returns NaN if `value` is NaN, `-limit` if `value` < `-limit`, `limit` if `value` > `limit` and `value` otherwise.

      Panics in debug if `limit` is negative or NaN.
      -/
      @[inline]
      def clampMagnitude (limit value : $sTy) : $sTy :=
        debug_assert! 1 / limit >= 0 && !limit.isNaN
        if value.isNaN
          then value
          else Max.max (-limit) (Min.min value limit)

      /-- Clamps `value` between 0 and 1. -/
      @[inline]
      def saturate (value : $sTy) : $sTy :=
        clamp value 0 1

      /--
      Returns a number that represents the sign of `value`.
      * 1 if `value` is positive, +0 or +Inf
      * -1 if `value` is negative, -0 or -Inf
      * NaN if `value` is NaN
      -/
      @[inline]
      def sign (value : $sTy) : $sTy :=
        if value.isNaN
          then value
          else if 1 / value >= 0
            then 1
            else -1

      /--
      Performs a linear interpolation between `start` and `end` based on the `value`.

      When `value` is `0`, the result will be `start`.
      When `value` is `1`, the result will be `end`.
      When `value` is outside of the range, the result is linearly extrapolated.

      Returns `NaN` if `value`, `start` or `end` is NaN.
      -/
      @[inline]
      def lerp (start «end» value : $sTy) : $sTy :=
        start + value * («end» - start)

      /--
      Returns `value` normalized to the range.

      When `value` is equal to `start` the result will be `0`.
      When `value` is equal to `end` the result will be `1`.
      When `value` is outside of the range, the result is linearly extrapolated.

      If `start` and `end` are equal, the result will be either infinite or NaN.
      Returns `NaN` if `value`, `start` or `end` is NaN.
      -/
      @[inline]
      def normalize (start «end» value : $sTy) : $sTy :=
        (value - start) / («end» - start)

      /--
      Remap `value` from the input range to the output range.

      When `value` is equal to `inputStart` this returns `outputStart`.
      When `value` is equal to `inputEnd` this returns `outputEnd`.

      When `value` is outside of the input range, the result is linearly extrapolated.

      If `inputStart` and `inputEnd` are equal, the result will be either infinite or NaN.
      Returns `NaN` if any of the inputs is NaN.
      -/
      @[inline]
      def remap (inputStart inputEnd outputStart outputEnd value : $sTy) : $sTy :=
        (value - inputStart) / (inputEnd - inputStart) * (outputEnd - outputStart) + outputStart

      /--
      Wraps `value` from `start` to `end`.

      Returns `value` with an integer number (floor) of `end - start` subtracted.

      Returns `NaN` if `value`, `start` or `end` is NaN or `start` equals `end`.
      -/
      @[inline]
      def wrap (start «end» value : $sTy) : $sTy :=
        let δ := «end» - start
        value - δ * ((value - start) / δ).floor

      end $cx.scalarExtNamespace
    )

/-- Positive infinity -/
@[inline]
def F32.inf : Float32 := .ofBits 0x7F800000

/-- Negative infinity -/
@[inline]
def F32.negInf : Float32 := .ofBits 0xFF800000

/-- Archimedes' constant (π) -/
@[inline]
def F32.pi : Float32 := .ofBits 0x40490FDB

/-- Positive infinity -/
@[inline]
def F64.inf : Float := .ofBits 0x7FF0000000000000

/-- Negative infinity -/
@[inline]
def F64.negInf : Float := .ofBits 0xFFF0000000000000

/-- Archimedes' constant (π) -/
@[inline]
def F64.pi : Float := .ofBits 0x400921FB54442D18
