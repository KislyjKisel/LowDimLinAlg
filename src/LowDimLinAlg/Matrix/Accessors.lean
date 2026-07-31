module

public import LowDimLinAlg.Axis
public import LowDimLinAlg.Matrix.Types

meta import LowDimLinAlg.Internal.Dimensionalities
meta import LowDimLinAlg.Internal.Scalars
meta import LowDimLinAlg.Internal.Syntax

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Lean Elab Command
open Internal

run_cmd
  let th : Nat → String := fun
    | 1 => "1st"
    | 2 => "2nd"
    | 3 => "3rd"
    | n => toString n ++ "th"
  for dims in dimensionalities do
    let axisTy := mkIdent <| .mkSimple s!"Axis{dims.size}"
    let dimsSizeLit := Syntax.mkNatLit dims.size
    let dimsSizeSqrLit := Syntax.mkNatLit <| dims.size * dims.size
    floats.forM fun cx => do
      let mTy := cx.structure <| "Matrix" ++ toString dims.size
      let vTy := cx.structure <| "Vector" ++ toString dims.size
      let sTy := cx.scalarType
      elabCommand <| ← `(namespace $mTy)
      for dim in dims do
        let rowFn := mkIdent <| .mkSimple s!"row{dim.index + 1}"
        let columnFn := mkIdent <| .mkSimple s!"column{dim.index + 1}"
        let axisFn := mkIdent <| .mkSimple s!"{dim.char}Axis"
        let setRowFn := mkIdent <| .mkSimple s!"setRow{dim.index + 1}"
        let setColumnFn := mkIdent <| .mkSimple s!"setColumn{dim.index + 1}"
        elabCommand <| ← `(
          @[inline]
          def $rowFn (m : $mTy) : $vTy :=
            ⟨$(dims.map fun dim2 => mget `m dim dim2):term,*⟩

          @[inline]
          def $columnFn (m : $mTy) : $vTy :=
            ⟨$(dims.map fun dim2 => mget `m dim2 dim):term,*⟩

          abbrev $axisFn := $rowFn

          @[inline]
          def $setRowFn (m : $mTy) (row : $vTy) : $mTy :=
            ⟨$(dims.flatMap fun i => dims.map fun j => if i == dim then vget `row j else mget `m i j):term,*⟩

          @[inline]
          def $setColumnFn (m : $mTy) (column : $vTy) : $mTy :=
            ⟨$(dims.flatMap fun i => dims.map fun j => if j == dim then vget `column i else mget `m i j):term,*⟩
        )
        let nth := th (dim.index + 1)
        addDocStringCore (← resolveGlobalConstNoOverload rowFn) <|
          s!"Returns the {nth} row as a vector.\n\n"
        addDocStringCore (← resolveGlobalConstNoOverload columnFn) <|
          s!"Returns the {nth} column as a vector.\n\n"
        addDocStringCore (← resolveGlobalConstNoOverload axisFn) <|
          s!"Returns the {nth} row as a vector.\n\n"
          ++ "For a transformation matrix that operates on **row vectors** this vector represents"
          ++ s!" the result of rotating the {dim.char.toUpper} axis by the matrix."
        addDocStringCore (← resolveGlobalConstNoOverload setRowFn) <|
          s!"Replaces the {nth} row by the provided vector.\n\n"
        addDocStringCore (← resolveGlobalConstNoOverload setColumnFn) <|
          s!"Replaces the {nth} column by the provided vector.\n\n"
      elabCommand <| ← `(
        /-- Returns the row with the specified index as a vector. -/
        @[inline]
        def row (m : $mTy) (i : Fin $dimsSizeLit) : $vTy :=
          match i with
          $(← dims.mapM fun dim => `(Lean.Parser.Term.matchAltExpr|
            | $(Syntax.mkNatLit dim.index)  => $(dot `m s!"row{dim.index + 1}")
          )):matchAlt*

        /-- Returns the column with the specified index as a vector. -/
        @[inline]
        def column (m : $mTy) (j : Fin $dimsSizeLit) : $vTy :=
          match j with
          $(← dims.mapM fun dim => `(Lean.Parser.Term.matchAltExpr|
            | $(Syntax.mkNatLit dim.index)  => $(dot `m s!"column{dim.index + 1}")
          )):matchAlt*

        /--
        Returns a vector that,
        for a transformation matrix that operates on **row vectors**,
        represents the result of rotating the specified axis by the matrix.
        -/
        @[inline]
        def axis (m : $mTy) (axis : $axisTy) : $vTy :=
          match axis with
          $(← dims.mapM fun dim => `(Lean.Parser.Term.matchAltExpr|
            | $(dot axisTy.getId dim.str)  => $(dot `m s!"row{dim.index + 1}")
          )):matchAlt*

        /-- Replaces the row with the specified index by the provided vector. -/
        @[inline]
        def setRow (m : $mTy) (i : Fin $dimsSizeLit) (row : $vTy) : $mTy :=
          match i with
          $(← dims.mapM fun dim => `(Lean.Parser.Term.matchAltExpr|
            | $(Syntax.mkNatLit dim.index) => $(dot `m s!"setRow{dim.index + 1}") row
          )):matchAlt*

        /-- Replaces the column with the specified index by the provided vector. -/
        @[inline]
        def setColumn (m : $mTy) (i : Fin $dimsSizeLit) (column : $vTy) : $mTy :=
          match i with
          $(← dims.mapM fun dim => `(Lean.Parser.Term.matchAltExpr|
            | $(Syntax.mkNatLit dim.index) => $(dot `m s!"setColumn{dim.index + 1}") column
          )):matchAlt*

        /-- Returns the element picked by its row and column indices. -/
        @[inline]
        def get (m : $mTy) (i j : Fin $dimsSizeLit) : $sTy :=
          match i, j with
          $(← dims.flatMapM fun i => dims.mapM fun j => `(Lean.Parser.Term.matchAltExpr|
            | $(Syntax.mkNatLit i.index), $(Syntax.mkNatLit j.index) => $(mget `m i j)
          )):matchAlt*

        /-- Replaces the element picked by its row and column indices. -/
        @[inline]
        def set (m : $mTy) (i j : Fin $dimsSizeLit) (x : $sTy) : $mTy :=
          match i, j with
          $(← dims.flatMapM fun i => dims.mapM fun j => `(Lean.Parser.Term.matchAltExpr|
            | $(Syntax.mkNatLit i.index), $(Syntax.mkNatLit j.index) =>
              { m with
                $(mkIdent <| .mkSimple s!"m{i.index + 1}{j.index + 1}"):ident := x
              }
          )):matchAlt*

        /-- Returns the element picked by its row-major index. -/
        @[inline]
        def getRm (m : $mTy) (i : Fin $dimsSizeSqrLit) : $sTy :=
          match i with
          $(← Std.IterM.toArray <| (0...(dims.size * dims.size)).iter.mapM fun idx => `(Lean.Parser.Term.matchAltExpr|
            | $(Syntax.mkNatLit idx) => $(dot `m s!"m{idx / dims.size + 1}{idx % dims.size + 1}")
          )):matchAlt*
          | ⟨n+$dimsSizeSqrLit, h⟩ => False.elim <|
            Nat.lt_irrefl $dimsSizeSqrLit (Nat.lt_of_le_of_lt (Nat.le_add_left $dimsSizeSqrLit n) h)

        /-- Returns the element picked by its column-major index. -/
        @[inline]
        def getCm (m : $mTy) (i : Fin $dimsSizeSqrLit) : $sTy :=
          match i with
          $(← Std.IterM.toArray <| (0...(dims.size * dims.size)).iter.mapM fun idx => `(Lean.Parser.Term.matchAltExpr|
            | $(Syntax.mkNatLit idx) => $(dot `m s!"m{idx % dims.size + 1}{idx / dims.size + 1}")
          )):matchAlt*
          | ⟨n+$dimsSizeSqrLit, h⟩ => False.elim <|
            Nat.lt_irrefl $dimsSizeSqrLit (Nat.lt_of_le_of_lt (Nat.le_add_left $dimsSizeSqrLit n) h)

        /-- Replaces the element picked by its row-major index. -/
        @[inline]
        def setRm (m : $mTy) (i : Fin $dimsSizeSqrLit) (x : $sTy) : $mTy :=
          match i with
          $(← Std.IterM.toArray <| (0...(dims.size * dims.size)).iter.mapM fun idx => `(Lean.Parser.Term.matchAltExpr|
            | $(Syntax.mkNatLit idx) =>
              { m with
                $(mkIdent <| .mkSimple s!"m{idx / dims.size + 1}{idx % dims.size + 1}"):ident := x
              }
          )):matchAlt*
          | ⟨n+$dimsSizeSqrLit, h⟩ => False.elim <|
            Nat.lt_irrefl $dimsSizeSqrLit (Nat.lt_of_le_of_lt (Nat.le_add_left $dimsSizeSqrLit n) h)

        /-- Replaces the element picked by its column-major index. -/
        @[inline]
        def setCm (m : $mTy) (i : Fin $dimsSizeSqrLit) (x : $sTy) : $mTy :=
          match i with
          $(← Std.IterM.toArray <| (0...(dims.size * dims.size)).iter.mapM fun idx => `(Lean.Parser.Term.matchAltExpr|
            | $(Syntax.mkNatLit idx) =>
              { m with
                $(mkIdent <| .mkSimple s!"m{idx % dims.size + 1}{idx / dims.size + 1}"):ident := x
              }
          )):matchAlt*
          | ⟨n+$dimsSizeSqrLit, h⟩ => False.elim <|
            Nat.lt_irrefl $dimsSizeSqrLit (Nat.lt_of_le_of_lt (Nat.le_add_left $dimsSizeSqrLit n) h)

        /-- Returns the diagonal of the matrix. -/
        @[inline]
        def diagonal (m : $mTy) : $vTy :=
          ⟨$(dims.map fun i => mget `m i i):term,*⟩

        end $mTy
      )
