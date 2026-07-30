module

public import LowDimLinAlg.Vector.Common

meta import LowDimLinAlg.Internal.Dimensionalities
meta import LowDimLinAlg.Internal.Scalars
meta import LowDimLinAlg.Internal.Syntax

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Lean Elab Command
open Internal

run_cmd
  for dims in dimensionalities do
    let bvTy := mkIdent <| Name.mkSimple <| "BVector" ++ toString dims.size
    scalars.forM fun cx => do
      if !cx.isNumber then return
      let sTy := cx.scalarType
      let vTy := cx.structure <| "Vector" ++ toString dims.size
      elabCommand <| ← `(
        namespace $vTy

        /-- Creates a vector with results of applying `f` to each component. -/
        @[inline]
        def mapBool (f : $sTy → Bool) (v : $vTy) : $bvTy :=
          $(app (bvTy.getId.str "mk") <| dims.map fun dim => app `f #[vget `v dim])

        /-- Componentwise addition (integers wrap on underflow and overflow). -/
        @[inline]
        def add (a b : $vTy) : $vTy :=
          $(app `mk <| dims.map fun dim => app ``Add.add #[vget `a dim, vget `b dim])

        /-- Componentwise subtraction (integers wrap on underflow and overflow). -/
        @[inline]
        def sub (a b : $vTy) : $vTy :=
          $(app `mk <| dims.map fun dim => app ``Sub.sub #[vget `a dim, vget `b dim])

        /-- Componentwise multiplication (integers wrap on underflow and overflow). -/
        @[inline]
        def mul (a b : $vTy) : $vTy :=
          $(app `mk <| dims.map fun dim => app ``Mul.mul #[vget `a dim, vget `b dim])

        /-- Componentwise division (integers wrap on underflow and overflow). -/
        @[inline]
        def div (a b : $vTy) : $vTy :=
          $(app `mk <| dims.map fun dim => app ``Div.div #[vget `a dim, vget `b dim])

        /-- Negation of a vector. -/
        @[inline]
        def neg (v : $vTy) : $vTy :=
          v.map (·.neg)

        /-- Componentwise multiplication of a vector by a scalar (integers wrap on underflow and overflow). -/
        @[inline]
        def scale (s : $sTy) (v : $vTy) : $vTy :=
          v.map (· * s)

        @[inline] instance : Add $vTy := ⟨add⟩
        @[inline] instance : Sub $vTy := ⟨sub⟩
        @[inline] instance : Mul $vTy := ⟨mul⟩
        @[inline] instance : Div $vTy := ⟨div⟩
        @[inline] instance : Neg $vTy := ⟨neg⟩
        @[inline] instance : SMul $sTy $vTy := ⟨scale⟩

        @[inline] instance : HMul $vTy $sTy $vTy := ⟨fun v s ↦ v.scale s⟩
        @[inline] instance : HMul $sTy $vTy $vTy := ⟨scale⟩

        @[inline]
        instance : HDiv $vTy $sTy $vTy :=
          ⟨fun v s ↦ ⟨$(dims.map fun dim => app ``Div.div #[vget `v dim, mkIdent `s]),*⟩⟩

        @[inline]
        instance : HDiv $sTy $vTy $vTy :=
          ⟨fun s v ↦ ⟨$(dims.map fun dim => app ``Div.div #[mkIdent `s, vget `v dim]),*⟩⟩

        @[inline]
        instance : HAdd $sTy $vTy $vTy :=
          ⟨fun s v ↦ ⟨$(dims.map fun dim => app ``Add.add #[mkIdent `s, vget `v dim]),*⟩⟩

        @[inline]
        instance : HAdd $vTy $sTy $vTy :=
          ⟨fun v s ↦ ⟨$(dims.map fun dim => app ``Add.add #[vget `v dim, mkIdent `s]),*⟩⟩

        @[inline]
        instance : HSub $sTy $vTy $vTy :=
          ⟨fun s v ↦ ⟨$(dims.map fun dim => app ``Sub.sub #[mkIdent `s, vget `v dim]),*⟩⟩

        @[inline]
        instance : HSub $vTy $sTy $vTy :=
          ⟨fun v s ↦ ⟨$(dims.map fun dim => app ``Sub.sub #[vget `v dim, mkIdent `s]),*⟩⟩

        /-- Sum of components. -/
        @[inline]
        def sum (v : $vTy) : $sTy :=
          $(foldBinopL dims ``Add.add fun dim => vget `v dim)

        /-- Product of components. -/
        @[inline]
        def product (v : $vTy) : $sTy :=
          $(foldBinopL dims ``Mul.mul fun dim => vget `v dim)

        /-- Dot product of two vectors. -/
        @[inline]
        def dot (a b : $vTy) : $sTy :=
          $(foldBinopL dims ``Add.add fun dim => app ``Mul.mul #[vget `a dim, vget `b dim])

        /-- Vector length squared. -/
        @[inline]
        def lengthSqr (v : $vTy) : $sTy :=
          dot v v
      )
      if cx.isSigned then
        if dims.size = 2 then
          elabCommand <| ← `(
            /-- Vector `v` rotated by 90 degrees counterclockwise (if Y is up and X is right). -/
            @[inline]
            def perpCCW (v : $vTy) : $vTy := ⟨-v.y, v.x⟩

            /-- Vector `v` rotated by 90 degrees clockwise (if Y is up and X is right). -/
            @[inline]
            def perpCW (v : $vTy) : $vTy := ⟨v.y, -v.x⟩

            /--
            Cross product of two 2D vectors extended to 3D by setting Z to 0.
            Returns Z of the resulting vector. Its X and Y are 0.

            Equal to the area of the parallelogram between the input vectors.
            Sign represents direction of rotation from `a` to `b`
            (negative means clockwise if Y is up and X is right).

            Equal to `|a||b| sin θ` where `θ` is the angle between vectors.
            -/
            @[inline]
            def cross (a b : $vTy) : $sTy :=
              a.x * b.y - a.y * b.x
          )
        if dims.size = 3 then
          elabCommand <| ← `(
            /--
            `|a||b|sin(θ)n`

            The cross product is defined as a vector that is orthogonal to both `a` and `b`
            and a magnitude equal to the area of the parallelogram with the vectors for sides.

            The direction is given by the right-hand rule for a right-handed coordinate system (e.g. X - right, Y - up, Z - towards viewer)
            and left-hand rule for a left-handed one (e.g. X - right, Y - up, Z - from viewer).

            `unitX × unitY = unitZ` where `x`, `y`, `z` - unit axis vectors.
            -/
            @[inline]
            def cross (a b : $vTy) : $vTy :=
              ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩
          )
        elabCommand <| ← `(
          /-- Computes absolute values of components. -/
          @[inline]
          def abs (v : $vTy) : $vTy :=
            ⟨$(dims.map fun dim => app (cx.scalarTypeName.str "abs") #[vget `v dim]),*⟩

          /-- Squared distance between two points. -/
          @[inline]
          def distanceSqr (a b : $vTy) : $sTy :=
            lengthSqr <| a - b
        )
      elabCommand <| ← `(end $vTy)
