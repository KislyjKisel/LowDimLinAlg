module

public section

namespace LowDimLinAlg

/-- 2D axis. -/
inductive Axis2 where
| x | y
deriving DecidableEq, Repr, Inhabited, Hashable

/-- 3D axis. -/
inductive Axis3 where
| x | y | z
deriving DecidableEq, Repr, Inhabited, Hashable

/-- Converts a 2D axis to 3D. -/
@[expose, inline]
def Axis2.toAxis3 : Axis2 → Axis3
| .x => .x
| .y => .y

/-- Converts a 3D axis to 2D returning `none` for `z`. -/
@[expose, inline]
def Axis3.toAxis2 : Axis3 → Option Axis2
| .x => some .x
| .y => some .y
| .z => none
