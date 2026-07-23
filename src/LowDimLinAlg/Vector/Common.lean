module

public import LowDimLinAlg.Axis
public import LowDimLinAlg.Vector.Boolean

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
    let dimsSizeLit := Lean.Syntax.mkNatLit dims.size
    let axisTy := mkIdent <| Name.mkSimple <| "Axis" ++ toString dims.size
    let bvTy := mkIdent <| Name.mkSimple <| "BVector" ++ toString dims.size
    scalars.forM fun cx => do
      let sTy := cx.scalarType
      let vTy := cx.structure <| "Vector" ++ toString dims.size
      let qIsNaN := Syntax.mkApp (cx.scalarMember "isNaN") ∘ Array.singleton
      elabCommand <| ← `(
        namespace $vTy

        /-- Converts a vector to a string of `(x y z w)` format.` -/
        @[inline]
        def toString (v : $vTy) : String :=
          $(Prod.snd <| flip dims.foldl (false, Syntax.mkStrLit "(") fun (separate, term) dim =>
            let field := app ``ToString.toString #[vget `v dim]
            Prod.mk true <| app ``String.append <| #[term].push <|
              if separate
                then app ``String.append #[Syntax.mkStrLit " ", field]
                else field
          ) ++ ")"

        @[inline]
        instance : ToString $vTy := ⟨toString⟩

        /-- Creates a vector with all elements set to `value`. -/
        @[inline]
        def splat (value : $sTy) : $vTy :=
          $(app `mk <| .replicate dims.size <| mkIdent `value)

        /-- Returns the vector component value indexed by an axis. -/
        @[inline]
        def get (v : $vTy) : $axisTy → $sTy
          $(← dims.mapM fun dim => `(Lean.Parser.Term.matchAltExpr|
            | .$dim.ident => $(vget `v dim)
          )):matchAlt*

        @[inline]
        instance : GetElem $vTy $axisTy $sTy (fun _ _ => True) where
          getElem := Function.curry <| Function.const _ ∘ get.uncurry

        @[inline]
        instance : GetElem $vTy Nat $sTy (fun _ i => i < $dimsSizeLit) where
          getElem v
          $(← dims.mapM fun dim => `(Lean.Parser.Term.matchAltExpr|
            | $dim.indexLit, _ => $(vget `v dim)
          )):matchAlt*

        /-- Sets the vector component value indexed by an axis. -/
        @[inline]
        def set (v : $vTy) : $axisTy → $sTy → $vTy
          $(← dims.mapM fun dim => `(Lean.Parser.Term.matchAltExpr|
            | .$dim.ident, $dim.ident => $(app `mk <| dims.map (fun d => vget `v d) |>.set! dim.index dim.ident)
          )):matchAlt*

        /-- Creates a vector with elements from `v` modified by `f`. -/
        @[inline]
        def map (f : $sTy → $sTy) (v : $vTy) : $vTy :=
          $(app `mk <| dims.map fun dim => app `f #[vget `v dim])

        /-- Creates a vector from an array. Panics if the list length is less than 2. -/
        @[inline]
        def ofList (a : List $sTy) : $vTy :=
          if h: a.length >= $dimsSizeLit
            then $(app `mk <| (0...dims.size).iter.map (fun i => app ``getElem #[mkIdent `a, Syntax.mkNatLit i, byGetElemTactic]) |>.toArray)
            else panic! $(Syntax.mkStrLit s!"list contains less than {dims.size} values")

        /-- Creates a vector from an array. Panics if the array size is less than 2. -/
        @[inline]
        def ofArray (a : Array $sTy) : $vTy :=
          if h: a.size >= $dimsSizeLit
            then $(app `mk <| (0...dims.size).iter.map (fun i => app ``getElem #[mkIdent `a, Syntax.mkNatLit i, byGetElemTactic]) |>.toArray)
            else panic! $(Syntax.mkStrLit s!"array contains less than {dims.size} values")

        /-- Creates a vector from a fixed length array. -/
        @[inline]
        def ofVector (v : Vector $sTy $dimsSizeLit) : $vTy :=
          $(app `mk <| (0...dims.size).iter.map (fun i => app ``getElem #[mkIdent `v, Syntax.mkNatLit i, byGetElemTactic]) |>.toArray)

        /-- Creates a list from vector components. -/
        @[inline]
        def toList (v : $vTy) : List $sTy :=
          [$(dims.map fun dim => vget `v dim),*]

        /-- Pushes vector components to an array. -/
        @[inline]
        def toArray (v : $vTy) (dst : Array $sTy := by exact Array.emptyWithCapacity $dimsSizeLit) : Array $sTy :=
          $(flip dims.foldl (mkIdent `dst) fun r dim => app ``Array.push #[r, vget `v dim])

        /-- Creates a fixed length array from vector components. -/
        @[inline]
        def toVector (v : $vTy) : Vector $sTy $dimsSizeLit :=
          $(flip dims.foldl (app ``Vector.emptyWithCapacity #[dimsSizeLit]) fun r dim => app ``Vector.push #[r, vget `v dim])

        /-- Creates a vector with components taken from two vectors selected by a `mask`. -/
        @[inline]
        def select (mask : $bvTy) (true false : $vTy) : $vTy :=
          $(app `mk <| dims.map fun dim => app ``cond #[vget `mask dim, vget `true dim, vget `false dim])

        /-- Minimal component of a vector. -/
        @[inline]
        def minValue (v : $vTy) : $sTy :=
          $(foldBinopL dims ``Min.min fun dim => vget `v dim)

        /-- Maximal component of a vector. -/
        @[inline]
        def maxValue (v : $vTy) : $sTy :=
          $(foldBinopL dims ``Max.max fun dim => vget `v dim)

        /--
        First minimal component axis.

        Panics in debug if any of the components is NaN.
        -/
        @[inline]
        def minAxis (v : $vTy) : $axisTy :=
          debug_assert! $(
            if cx.isFloat
              then foldBinopL dims ``Bool.and fun dim => qIsNaN <| vget `v dim
              else mkIdent ``true
          )
          $(
            let qIsMinimal (dim : Dimension) : TSyntax `term :=
              foldBinopL (dims.filter (·.index != dim.index)) ``Bool.and fun dim2 =>
                app ``LE.le #[vget `v dim, vget `v dim2]
            flip (dims.take <| dims.size - 1).foldr (dot axisTy.getId dims[dims.size - 1]!.str) fun dim r =>
              app ``cond #[qIsMinimal dim, dot axisTy.getId dim.str, r]
          )

        /--
        First maximal component axis.

        Panics in debug if any of the components is NaN.
        -/
        @[inline]
        def maxAxis (v : $vTy) : $axisTy :=
          debug_assert! $(
            if cx.isFloat
              then foldBinopL dims ``Bool.and fun dim => qIsNaN <| vget `v dim
              else mkIdent ``true
          )
          $(
            let qIsMaximal (dim : Dimension) : TSyntax `term :=
              foldBinopL (dims.filter (·.index != dim.index)) ``Bool.and fun dim2 =>
                app ``LE.le #[vget `v dim2, vget `v dim]
            flip (dims.take <| dims.size - 1).foldr (dot axisTy.getId dims[dims.size - 1]!.str) fun dim r =>
              app ``cond #[qIsMaximal dim, dot axisTy.getId dim.str, r]
          )

        /-- Returns `true` if application of `f` to *any* of the components returns `true`. -/
        @[inline]
        def any (f : $sTy → Bool) (v : $vTy) : Bool :=
          $(foldBinopL dims ``Bool.or fun dim => app `f #[vget `v dim])

        /-- Returns `true` if application of `f` to *each* component returns `true`. -/
        @[inline]
        def all (f : $sTy → Bool) (v : $vTy) : Bool :=
          $(foldBinopL dims ``Bool.and fun dim => app `f #[vget `v dim])

        /-- Componentwise minimum. -/
        @[inline]
        def min (a b : $vTy) : $vTy :=
          $(app `mk <| dims.map fun dim => app ``Min.min #[vget `a dim, vget `b dim])

        /-- Componentwise maximum. -/
        @[inline]
        def max (a b : $vTy) : $vTy :=
          $(app `mk <| dims.map fun dim => app ``Max.max #[vget `a dim, vget `b dim])

        /-- Componentwise "less than". -/
        @[inline]
        def lt' (a b : $vTy) : $bvTy :=
          $(app (bvTy.getId.str "mk") <| dims.map fun dim => app ``LT.lt #[vget `a dim, vget `b dim])

        /-- Componentwise "less than or equal to". -/
        @[inline]
        def le' (a b : $vTy) : $bvTy :=
          $(app (bvTy.getId.str "mk") <| dims.map fun dim => app ``LE.le #[vget `a dim, vget `b dim])

        /-- Componentwise "greater than". -/
        @[inline]
        def gt' (a b : $vTy) : $bvTy :=
          $(app (bvTy.getId.str "mk") <| dims.map fun dim => app ``LT.lt #[vget `b dim, vget `a dim])

        /-- Componentwise "greater than or equal to". -/
        @[inline]
        def ge' (a b : $vTy) : $bvTy :=
          $(app (bvTy.getId.str "mk") <| dims.map fun dim => app ``LE.le #[vget `b dim, vget `a dim])

        /-- Whether componentwise "less than" is true on all axes. -/
        @[inline]
        def lt (a b : $vTy) : Prop :=
          $(foldBinopR dims ``And fun dim => app ``LT.lt #[vget `a dim, vget `b dim])

        /-- Whether componentwise "less than or equal to" is true on all axes. -/
        @[inline]
        def le (a b : $vTy) : Prop :=
          $(foldBinopR dims ``And fun dim => app ``LE.le #[vget `a dim, vget `b dim])

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

        end $vTy
      )
