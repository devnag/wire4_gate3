import Proof.Quartic.StageNativeKidsPrice.SourcePrices

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPrice

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open NearCubicGates.Close.TabMachine NearCubicGates.Close.Dispatch
open StageNativeKids StageTuple StagePrint

/-- `lem:print`, paper/paper.tex: one row
case additionally retains an actual original exact-child index. -/
structure RowCase extends SourceCase where
  childIndex : Fin (exactChildren (callAtoms request.header.call
    (request.toRowContext.originalIndex request.atom))).length

/-- `lem:print`, paper/paper.tex: each row
case is the existing concrete original-source pipeline call. -/
def RowCase.pipeline : (a : RowCase) → OriginalPipelineRequest a.second
  | ⟨⟨r, false, h⟩, j⟩ => r.toRowContext.firstPipeline r.atom h j
  | ⟨⟨r, true, h⟩, j⟩ => r.toRowContext.secondPipeline r.atom h j

/-- `prop:time`, paper/paper.tex: a row
uses the same original request resource as its source counter. -/
def RowCase.scale (a : RowCase) : ℕ := a.toSourceCase.scale

/-- `prop:time`, paper/paper.tex: this
structural scale is positive for every actual row case. -/
theorem row_scale_pos (a : RowCase) : 1 ≤ a.scale := scale_pos a.toSourceCase

/-- `lem:print`, paper/paper.tex: row and
count calls select the same actual original bank occurrence. -/
theorem row_source (a : RowCase) : a.pipeline.source = a.toSourceCase.source := by
  rcases a with ⟨⟨r, b, h⟩, j⟩
  cases b <;> rfl

/-- `lem:print`, paper/paper.tex: the row
pipeline retains the source selector's original exact compiler request. -/
theorem row_original (a : RowCase) : a.pipeline.row.original = a.toSourceCase.source.child :=
  a.pipeline.original_eq.trans (congrArg (fun s => s.child) (row_source a))

/-- `lem:print`, paper/paper.tex: the
actual scalar header is shared by every original child of the atom. -/
theorem row_header (a : RowCase) : a.pipeline.row.header a.pipeline.row.fields_fit =
    a.request.toRowContext.rowHeader a.request.atom := by
  rcases a with ⟨⟨r, b, h⟩, j⟩
  cases b <;> exact r.toRowContext.originalRow_header r.atom j

/-- `imp:pullback`, paper/paper.tex: the
same canonical original dimension controls the real affine row request. -/
theorem row_dimension (a : RowCase) :
    a.pipeline.row.canonicalPullback.parameters.n = a.request.header.call.n := by
  rcases a with ⟨⟨r, b, h⟩, j⟩
  cases b <;> rfl

/-- `lem:print`, paper/paper.tex: the
ten actual natural metadata fields and three flags have a fixed
original-arity bit bound, without enumerating a numeric walk value. -/
theorem header_length (r : RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length)) :
    (r.rowHeader i).length ≤ 1000*(r.header.call.n+1)^4 := by
  have hh := flatMap_length_le (r.rolePacket i).outputValues natWord
    (2*(35*(r.header.call.n+1)^4)+1) (by
      intro v hv
      have hb := role_output_bits r i v hv
      simp only [NearCubicGates.Close.Dispatch.natWord_length]
      omega)
  have hl : (r.rolePacket i).outputValues.length = 10 := by
    simp [RolePacket.outputValues]
  rw [hl] at hh
  have hout : (r.rolePacket i).output.length =
      ((r.rolePacket i).outputValues.flatMap natWord).length+3 := by
    simp only [RolePacket.output, List.length_append, List.length_cons, List.length_nil]
  rw [role_output] at hout
  have hp : 1 ≤ (r.header.call.n+1)^4 := Nat.one_le_pow _ _ (by omega)
  simp only [List.length_append] at hout
  omega

/-- `prop:time`, paper/paper.tex: the
actual pipeline header has a uniform polynomial structural price. -/
theorem row_header_price : Price RowCase.scale
    (fun a => (a.pipeline.row.header a.pipeline.row.fields_fit).length) := by
  have hn : Price RowCase.scale (fun a => a.request.header.call.n) :=
    arity_price.comp RowCase.toSourceCase
  have h : Price RowCase.scale (fun a => 1000*(a.request.header.call.n+1)^4) := by
    price_with row_scale_pos
  apply h.mono
  intro a
  rw [row_header]
  exact header_length a.request.toRowContext a.request.atom

/-- `prop:time`, paper/paper.tex: the
literal unary compiler index is bounded by the unchanged sharp original
child cap and hence by the actual structural resource. -/
theorem row_index_price : Price RowCase.scale (fun a => a.pipeline.row.compilerIndex.val) := by
  have hc := child_count_price.comp RowCase.toSourceCase
  apply hc.mono
  intro a
  have hi := a.pipeline.row.compilerIndex.isLt
  exact hi.le.trans_eq (congrArg
    (fun r => (compileL r.weights r.target).length) (row_original a))

/-- `prop:time`, paper/paper.tex: the row
retains the polynomial width of its actual original compiler request. -/
theorem row_field_price : Price RowCase.scale (fun a => a.pipeline.row.original.W) := by
  have h : Price RowCase.scale (fun a => a.toSourceCase.source.child.W) :=
    field_price.comp RowCase.toSourceCase
  exact h.mono fun a => (congrArg (fun r => r.W) (row_original a)).le

/-- `prop:time`, paper/paper.tex: the row
retains the original dense arity of its actual compiler request. -/
theorem row_weights_price : Price RowCase.scale
    (fun a => a.pipeline.row.original.weights.length) := by
  have h : Price RowCase.scale (fun a => a.toSourceCase.source.child.weights.length) :=
    weights_price.comp RowCase.toSourceCase
  exact h.mono fun a => (congrArg (fun r => r.weights.length) (row_original a)).le

/-- `prop:time`, paper/paper.tex: the
actual row compiler retains the unchanged original child census. -/
theorem row_count_price : Price RowCase.scale
    (fun a => (compileL a.pipeline.row.original.weights a.pipeline.row.original.target).length) := by
  have h : Price RowCase.scale (fun a =>
      (compileL a.toSourceCase.source.child.weights a.toSourceCase.source.child.target).length) :=
    child_count_price.comp RowCase.toSourceCase
  exact h.mono fun a => (congrArg (fun r => (compileL r.weights r.target).length) (row_original a)).le

/-- `lem:print`, paper/paper.tex: the
selected original row has its exact dense signed-byte length. -/
theorem row_body_length (a : RowCase) : a.pipeline.rowBody.length =
    (a.pipeline.row.original.weights.length+1)*(a.pipeline.row.original.W+1) := by
  have hl := compileL_length a.pipeline.row.original.weights a.pipeline.row.original.target
    (compileL a.pipeline.row.original.weights a.pipeline.row.original.target)[a.pipeline.row.compilerIndex.val]
    (List.getElem_mem a.pipeline.row.compilerIndex.isLt)
  simp only [OriginalPipelineRequest.rowBody, recBits, List.length_flatMap,
    SignedSortKey.binary_length, List.map_const', List.sum_replicate, smul_eq_mul, hl]

/-- `prop:time`, paper/paper.tex: the
actual selected dense row byte width has a uniform structural price. -/
theorem row_body_price : Price RowCase.scale (fun a => a.pipeline.rowBody.length) := by
  have hw := row_field_price
  have hn := row_weights_price
  have h : Price RowCase.scale (fun a =>
      (a.pipeline.row.original.weights.length+1)*(a.pipeline.row.original.W+1)) := by
    price_with row_scale_pos
  exact h.mono fun a => (row_body_length a).le

end NearQuarticWires.StageNativeKidsPrice
