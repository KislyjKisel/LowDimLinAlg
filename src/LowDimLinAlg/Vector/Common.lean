module

public import LowDimLinAlg.Axis
public import LowDimLinAlg.Vector.Boolean

import LowDimLinAlg.Meta.Dimensionalities
import LowDimLinAlg.Meta.Scalars

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Lean Elab Command

run_cmd
  let q0 := Lean.Syntax.mkNatLit 0
  let q1 := Lean.Syntax.mkNatLit 1
  let appN (f : Name) : TSyntaxArray `term → TSyntax `term := Syntax.mkApp (mkIdent f)
  let qAppend (a b : TSyntax `term) : TSyntax `term := appN ``Append.append #[a, b]
  let byGetElemTactic ← `(by get_elem_tactic)
  let mapReduceL {α : Type} (xs : Array α) (op : Lean.Name) (f : α → TSyntax `term) : TSyntax `term :=
    xs.foldl (fun | none, x => f x | (some s), x => appN op #[s, f x]) none |>.get!
  let mapReduceR {α : Type} (xs : Array α) (op : Lean.Name) (f : α → TSyntax `term) : TSyntax `term :=
    xs.foldr (fun | x, none => f x | x, (some s) => appN op #[f x, s]) none |>.get!
  let vGet (var : Name) (dimChar : Char) : Ident := mkIdent <| var.str dimChar.toString
  let vGet' (var : Name) (dim : Meta.Dimension) : Ident := vGet var dim.char
  for dims in Meta.dimensionalities 2 4 do
    let dimsSizeLit := Lean.Syntax.mkNatLit dims.size
    let axisTy := mkIdent <| Name.mkSimple <| "Axis" ++ toString dims.size
    let axisCon := mkIdent ∘ axisTy.getId.str
    let bvTy := mkIdent <| Name.mkSimple <| "BVector" ++ toString dims.size
    Meta.scalars.forM fun cx => do
      let sTy := cx.scalarType
      let vTy := mkIdent <| Name.mkSimple <| cx.scalarPrefix ++ "Vector" ++ toString dims.size
      let qIsNaN := Syntax.mkApp (cx.scalarMember "isNaN") ∘ Array.singleton
      if cx.isNumber then
        elabCommand <| ← `(
          structure $vTy where
            $(← dims.mapM fun dim => `(Parser.Command.structSimpleBinder|
              $dim.ident:ident : $sTy
            )):structSimpleBinder*
          deriving Repr, Inhabited
        )
      elabCommand <| ← `(
        namespace $vTy

        /-- Converts a vector to a string of `(x y z w)` format.` -/
        @[inline]
        def toString (v : $vTy) : String :=
          $(Prod.snd <| flip dims.foldl (false, Syntax.mkStrLit "(") fun (separate, term) dim =>
            let field := Syntax.mkApp (mkIdent ``ToString.toString) #[vGet' `v dim]
            Prod.mk true <| qAppend term <| if separate then qAppend (Syntax.mkStrLit " ") field else field
          ) ++ ")"

        @[inline]
        instance : ToString $vTy := ⟨toString⟩

        /-- Creates a vector with all elements set to `value`. -/
        @[inline]
        def splat (value : $sTy) : $vTy :=
          $(appN `mk <| .replicate dims.size <| mkIdent `value)

        /-- Gets vector's component value. -/
        @[inline]
        def get (v : $vTy) : $axisTy → $sTy
          $(← dims.mapM fun dim => `(Lean.Parser.Term.matchAltExpr|
            | .$dim.ident => $(vGet' `v dim)
          )):matchAlt*

        @[inline]
        instance : GetElem $vTy $axisTy $sTy (fun _ _ => True) where
          getElem := Function.curry <| Function.const _ ∘ get.uncurry

        @[inline]
        instance : GetElem $vTy Nat $sTy (fun _ i => i < $dimsSizeLit) where
          getElem v
          $(← dims.mapM fun dim => `(Lean.Parser.Term.matchAltExpr|
            | $dim.indexLit, _ => $(vGet' `v dim)
          )):matchAlt*

        /-- Sets vector's component value. -/
        @[inline]
        def set (v : $vTy) : $axisTy → $sTy → $vTy
          $(← dims.mapM fun dim => `(Lean.Parser.Term.matchAltExpr|
            | .$dim.ident, $dim.ident => $(appN `mk <| dims.map (fun d => vGet' `v d) |>.set! dim.index dim.ident)
          )):matchAlt*

        /-- Creates a vector with elements from `v` modified by `f`. -/
        @[inline]
        def map (f : $sTy → $sTy) (v : $vTy) : $vTy :=
          $(appN `mk <| dims.map fun dim => appN `f #[vGet' `v dim])

        /-- Creates a vector from an array. Panics if the list's length is less than 2. -/
        @[inline]
        def ofList (a : List $sTy) : $vTy :=
          if h: a.length >= $dimsSizeLit
            then $(appN `mk <| (0...dims.size).iter.map (fun i => appN ``getElem #[mkIdent `a, Syntax.mkNatLit i, byGetElemTactic]) |>.toArray)
            else panic! $(Syntax.mkStrLit s!"list contains less than {dims.size} values")

        /-- Creates a vector from an array. Panics if the array's size is less than 2. -/
        @[inline]
        def ofArray (a : Array $sTy) : $vTy :=
          if h: a.size >= $dimsSizeLit
            then $(appN `mk <| (0...dims.size).iter.map (fun i => appN ``getElem #[mkIdent `a, Syntax.mkNatLit i, byGetElemTactic]) |>.toArray)
            else panic! $(Syntax.mkStrLit s!"array contains less than {dims.size} values")

        /-- Creates a vector from a fixed length array. -/
        @[inline]
        def ofVector (v : Vector $sTy $dimsSizeLit) : $vTy :=
          $(appN `mk <| (0...dims.size).iter.map (fun i => appN ``getElem #[mkIdent `v, Syntax.mkNatLit i, byGetElemTactic]) |>.toArray)

        /-- Creates a list from vector components. -/
        @[inline]
        def toList (v : $vTy) : List $sTy :=
          [$(dims.map fun dim => vGet' `v dim),*]

        /-- Pushes vector components to an array. -/
        @[inline]
        def toArray (v : $vTy) (dst : Array $sTy := by exact Array.emptyWithCapacity $dimsSizeLit) : Array $sTy :=
          $(flip dims.foldl (mkIdent `dst) fun r dim => appN ``Array.push #[r, vGet' `v dim])

        /-- Creates a fixed length array from vector components. -/
        @[inline]
        def toVector (v : $vTy) : Vector $sTy $dimsSizeLit :=
          $(flip dims.foldl (appN ``Vector.emptyWithCapacity #[dimsSizeLit]) fun r dim => appN ``Vector.push #[r, vGet' `v dim])

        @[inline]
        def select (mask : $bvTy) (true false : $vTy) : $vTy :=
          $(appN `mk <| dims.map fun dim => appN ``cond #[vGet' `mask dim, vGet' `true dim, vGet' `false dim])

        /-- Minimal component of a vector. -/
        @[inline]
        def minValue (v : $vTy) : $sTy :=
          $(mapReduceL dims ``Min.min fun dim => vGet' `v dim)

        /-- Maximal component of a vector. -/
        @[inline]
        def maxValue (v : $vTy) : $sTy :=
          $(mapReduceL dims ``Max.max fun dim => vGet' `v dim)

        /--
        First minimal component axis.

        Panics in debug if any of the components is NaN.
        -/
        @[inline]
        def minAxis (v : $vTy) : $axisTy :=
          debug_assert! $(
            if cx.isFloat
              then mapReduceL dims ``Bool.and fun dim => qIsNaN <| vGet' `v dim
              else mkIdent ``true
          )
          $(
            let qIsMinimal (dim : Meta.Dimension) : TSyntax `term :=
              mapReduceL (dims.filter (·.index != dim.index)) ``Bool.and fun dim2 =>
                appN ``LE.le #[vGet' `v dim, vGet' `v dim2]
            flip (dims.take <| dims.size - 1).foldr (axisCon dims[dims.size - 1]!.str) fun dim r =>
              appN ``cond #[qIsMinimal dim, axisCon dim.str, r]
          )

        /--
        First maximal component axis.

        Panics in debug if any of the components is NaN.
        -/
        @[inline]
        def maxAxis (v : $vTy) : $axisTy :=
          debug_assert! $(
            if cx.isFloat
              then mapReduceL dims ``Bool.and fun dim => qIsNaN <| vGet' `v dim
              else mkIdent ``true
          )
          $(
            let qIsMaximal (dim : Meta.Dimension) : TSyntax `term :=
              mapReduceL (dims.filter (·.index != dim.index)) ``Bool.and fun dim2 =>
                appN ``LE.le #[vGet' `v dim2, vGet' `v dim]
            flip (dims.take <| dims.size - 1).foldr (axisCon dims[dims.size - 1]!.str) fun dim r =>
              appN ``cond #[qIsMaximal dim, axisCon dim.str, r]
          )

          /-- Returns `true` if application of `f` to *any* of the components returns `true`. -/
          @[inline]
          def any (f : $sTy → Bool) (v : $vTy) : Bool :=
            $(mapReduceL dims ``Bool.or fun dim => appN `f #[vGet' `v dim])

          /-- Returns `true` if application of `f` to *each* component returns `true`. -/
          @[inline]
          def all (f : $sTy → Bool) (v : $vTy) : Bool :=
            $(mapReduceL dims ``Bool.and fun dim => appN `f #[vGet' `v dim])

          /-- Componentwise minimum. -/
          @[inline]
          def min (a b : $vTy) : $vTy :=
            $(appN `mk <| dims.map fun dim => appN ``Min.min #[vGet' `a dim, vGet' `b dim])

          /-- Componentwise maximum. -/
          @[inline]
          def max (a b : $vTy) : $vTy :=
            $(appN `mk <| dims.map fun dim => appN ``Max.max #[vGet' `a dim, vGet' `b dim])

          /-- Componentwise "less than". -/
          @[inline]
          def lt' (a b : $vTy) : $bvTy :=
            $(appN (bvTy.getId.str "mk") <| dims.map fun dim => appN ``LT.lt #[vGet' `a dim, vGet' `b dim])

          /-- Componentwise "less than or equal to". -/
          @[inline]
          def le' (a b : $vTy) : $bvTy :=
            $(appN (bvTy.getId.str "mk") <| dims.map fun dim => appN ``LE.le #[vGet' `a dim, vGet' `b dim])

          /-- Componentwise "greater than". -/
          @[inline]
          def gt' (a b : $vTy) : $bvTy :=
            $(appN (bvTy.getId.str "mk") <| dims.map fun dim => appN ``LT.lt #[vGet' `b dim, vGet' `a dim])

          /-- Componentwise "greater than or equal to". -/
          @[inline]
          def ge' (a b : $vTy) : $bvTy :=
            $(appN (bvTy.getId.str "mk") <| dims.map fun dim => appN ``LE.le #[vGet' `b dim, vGet' `a dim])

          /-- Whether componentwise "less than" is true on all axes. -/
          @[inline]
          def lt (a b : $vTy) : Prop :=
            $(mapReduceR dims ``And fun dim => appN ``LT.lt #[vGet' `a dim, vGet' `b dim])

          /-- Whether componentwise "less than or equal to" is true on all axes. -/
          @[inline]
          def le (a b : $vTy) : Prop :=
            $(mapReduceR dims ``And fun dim => appN ``LE.le #[vGet' `a dim, vGet' `b dim])

          @[inline] instance : LT $vTy := ⟨lt⟩
          @[inline] instance : LE $vTy := ⟨le⟩

          @[inline]
          instance : DecidableLT $vTy := fun _ _ => by
            unfold LT.lt instLT lt
            infer_instance

          @[inline]
          instance : DecidableLE $vTy := fun _ _ => by
            unfold LE.le instLE le
            infer_instance
      )
      if cx.isNumber then
        elabCommand <| ← `(
          /-- Creates a vector with results of applying `f` to each component. -/
          @[inline]
          def mapBool (f : $sTy → Bool) (v : $vTy) : $bvTy :=
            $(appN (bvTy.getId.str "mk") <| dims.map fun dim => appN `f #[vGet' `v dim])

          /-- All components set to 0. -/
          @[inline]
          def zero : $vTy :=
            ⟨$(Array.replicate dims.size q0),*⟩

          /-- All components set to 1. -/
          @[inline]
          def one : $vTy :=
            ⟨$(Array.replicate dims.size q1),*⟩

          /-- All components set to -1. -/
          @[inline]
          def negOne : $vTy :=
            ⟨$(Array.replicate dims.size <| Lean.Syntax.mkApp (Lean.mkIdent ``Neg.neg) <| #[q1]),*⟩

          /-- Componentwise addition (integers wrap on underflow and overflow). -/
          @[inline]
          def add (a b : $vTy) : $vTy :=
            $(appN `mk <| dims.map fun dim => appN ``Add.add #[vGet' `a dim, vGet' `b dim])

          /-- Componentwise subtraction (integers wrap on underflow and overflow). -/
          @[inline]
          def sub (a b : $vTy) : $vTy :=
            $(appN `mk <| dims.map fun dim => appN ``Sub.sub #[vGet' `a dim, vGet' `b dim])

          /-- Componentwise multiplication (integers wrap on underflow and overflow). -/
          @[inline]
          def mul (a b : $vTy) : $vTy :=
            $(appN `mk <| dims.map fun dim => appN ``Mul.mul #[vGet' `a dim, vGet' `b dim])

          /-- Componentwise division (integers wrap on underflow and overflow). -/
          @[inline]
          def div (a b : $vTy) : $vTy :=
            $(appN `mk <| dims.map fun dim => appN ``Div.div #[vGet' `a dim, vGet' `b dim])

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
          @[inline] instance : HDiv $vTy $sTy $vTy := ⟨fun v s ↦ v.scale (1 / s)⟩

          @[inline]
          instance : HDiv $sTy $vTy $vTy :=
            ⟨fun s v ↦ ⟨$(dims.map fun dim => appN ``Div.div #[mkIdent `s, vGet' `v dim]),*⟩⟩

          @[inline]
          instance : HAdd $sTy $vTy $vTy :=
            ⟨fun s v ↦ ⟨$(dims.map fun dim => appN ``Add.add #[mkIdent `s, vGet' `v dim]),*⟩⟩

          @[inline]
          instance : HAdd $vTy $sTy $vTy :=
            ⟨fun v s ↦ ⟨$(dims.map fun dim => appN ``Add.add #[vGet' `v dim, mkIdent `s]),*⟩⟩

          @[inline]
          instance : HSub $sTy $vTy $vTy :=
            ⟨fun s v ↦ ⟨$(dims.map fun dim => appN ``Sub.sub #[mkIdent `s, vGet' `v dim]),*⟩⟩

          @[inline]
          instance : HSub $vTy $sTy $vTy :=
            ⟨fun v s ↦ ⟨$(dims.map fun dim => appN ``Sub.sub #[vGet' `v dim, mkIdent `s]),*⟩⟩

          /-- Sum of components. -/
          @[inline]
          def sum (v : $vTy) : $sTy :=
            $(mapReduceL dims ``Add.add fun dim => vGet' `v dim)

          /-- Product of components. -/
          @[inline]
          def product (v : $vTy) : $sTy :=
            $(mapReduceL dims ``Mul.mul fun dim => vGet' `v dim)

          /-- Dot product of two vectors. -/
          @[inline]
          def dot (a b : $vTy) : $sTy :=
            $(mapReduceL dims ``Add.add fun dim => appN ``Mul.mul #[vGet' `a dim, vGet' `b dim])

          /-- Vector length squared. -/
          @[inline]
          def lengthSqr (v : $vTy) : $sTy :=
            dot v v
        )
      for dim in dims do
        let fId := mkIdent <| Name.mkSimple s!"with{dim.char.toUpper}"
        elabCommand <| ← `(
          @[inline]
          def $fId (v : $vTy) (value : $sTy) : $vTy :=
            $(appN `mk <| Array.set! (dims.map fun d => vGet' `v d) dim.index (mkIdent `value))
        )
        addDocStringCore (← resolveGlobalConstNoOverload fId)
          s!"Creates a vector `⟨{", ".intercalate <| Array.toList <| dims.map fun d => if d.index == dim.index then "value" else s!"v.{d.char}"}⟩`."
        if cx.isNumber then
          let unitPosId := mkIdent <| Name.mkSimple s!"unit{dim.char.toUpper}"
          let unitNegId := mkIdent <| Name.mkSimple s!"unitNeg{dim.char.toUpper}"
          elabCommand <| ← `(
            @[inline]
            def $unitPosId : $vTy :=
              $(appN `mk <| dims.map fun d => if d.index == dim.index then q1 else q0)

            @[inline]
            def $unitNegId : $vTy :=
              $(appN `mk <| dims.map fun d => if d.index == dim.index then appN ``Neg.neg #[q1] else q0)
          )
          addDocStringCore (← resolveGlobalConstNoOverload unitPosId)
            s!"A unit vector pointing along the positive {dim.char.toUpper} axis."
          addDocStringCore (← resolveGlobalConstNoOverload unitNegId)
            s!"A unit vector pointing along the negative {dim.char.toUpper} axis."
      elabCommand <| ← `(end $vTy)
