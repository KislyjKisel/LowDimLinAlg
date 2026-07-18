module

@[expose] public section

namespace LowDimLinAlg

/-- 2D axis. -/
inductive Axis2 where
| x | y
deriving DecidableEq, Repr, Inhabited, Hashable

/-- 3D axis. -/
inductive Axis3 where
| x | y | z
deriving DecidableEq, Repr, Inhabited, Hashable

/-- 4D axis. -/
inductive Axis4 where
| x | y | z | w
deriving DecidableEq, Repr, Inhabited, Hashable

/-- Converts a 2D axis to 3D. -/
@[inline]
def Axis2.toAxis3 : Axis2 → Axis3
| .x => .x
| .y => .y

/-- Converts a 2D axis to 4D. -/
@[inline]
def Axis2.toAxis4 : Axis2 → Axis4
| .x => .x
| .y => .y

/-- Converts a 3D axis to 4D. -/
@[inline]
def Axis3.toAxis4 : Axis3 → Axis4
| .x => .x
| .y => .y
| .z => .z

/-- Converts a 3D axis to 2D returning `none` for `z`. -/
@[inline]
def Axis3.toAxis2 : Axis3 → Option Axis2
| .x => some .x
| .y => some .y
| .z => none

/-- Converts a 4D axis to 2D returning `none` for `z` and `w`. -/
@[inline]
def Axis4.toAxis2 : Axis4 → Option Axis2
| .x => some .x
| .y => some .y
| .z => none
| .w => none

/-- Converts a 4D axis to 3D returning `none` for `w`. -/
@[inline]
def Axis4.toAxis3 : Axis4 → Option Axis3
| .x => some .x
| .y => some .y
| .z => some .z
| .w => none

instance : Coe Axis2 Axis3 := ⟨Axis2.toAxis3⟩
instance : Coe Axis3 Axis4 := ⟨Axis3.toAxis4⟩
