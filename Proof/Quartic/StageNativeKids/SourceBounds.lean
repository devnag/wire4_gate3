import Proof.Quartic.StageNativeKids.BankMachine
import Proof.Quartic.StageNativeKids.AcquireMachine
import Proof.Quartic.StageNativeKidsPrice.Rows
import Proof.Quartic.StageNativeKidsPrice.Cap
import Proof.Gates.CellsPack.Lang

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Cells
open StageTuple StagePrint StagePrint.Header StageNativeKidsPrice

/-- `prop:time`, paper/paper.tex: the one-atom
source resource includes only its finite original word, original arity,
original sharp child cap and actual target field width. -/
def NativeKidsRequest.structuralScale (r : NativeKidsRequest) : ℕ :=
  r.originalSourceScale + r.outputWidth + 1

/-- `prop:time`, paper/paper.tex: every
actual one-atom source has a positive structural resource. -/
theorem structuralScale_pos (r : NativeKidsRequest) : 1 ≤ r.structuralScale := by
  unfold NativeKidsRequest.structuralScale
  omega

/-- `lem:print`, paper/paper.tex: the
literal eleven-field source has exactly its actual nested framing cost. -/
theorem native_word_length (r : NativeKidsRequest) :
    r.word.length = 4 * (callWord r.header.call).length +
      4 * ((baseHeaderValues r.header).flatMap natWord).length +
      2 * r.contextWord.length + 2 * (natWord r.atom.val).length +
      2 * (natWord r.outputWidth).length + 15 := by
  simp [NativeKidsRequest.word, NativeKidsRequest.sourceFields, Top.loadRec, frame_length]
  omega

/-- `lem:print`, paper/paper.tex: the
actual role reply replaces one empty acquired field, preserving every
original source byte and adding only its literal doubled frame payload. -/
theorem acquired_word_length (r : NativeKidsRequest) :
    r.acquiredWord.length = r.word.length + 2 * r.rolePayload.length := by
  simp only [NativeKidsRequest.acquiredWord, NativeKidsRequest.word, Top.loadRec,
    List.length_append, frame_length, NativeKidsRequest.sourceFields]
  simp
  omega

/-- `prop:time`, paper/paper.tex: the
actual eleven-field loader pays a linear price in its entire encoded
source, independently of every numeric radix and walk value. -/
theorem original_loader_cost (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    Top.loadCost f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 =
      6 * (Top.loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10).length + 27 := by
  simp only [Top.loadCost, Top.loadChainCost, Top.loadRec, List.length_append, frame_length]
  omega

/-- `prop:time`, paper/paper.tex: arity
has a direct structural source price. -/
theorem native_arity_price :
    Price NativeKidsRequest.structuralScale (fun r => r.header.call.n) :=
  Price.of_le (by intro r; unfold NativeKidsRequest.structuralScale NativeKidsRequest.originalSourceScale; omega)

/-- `prop:time`, paper/paper.tex: literal
original source length has a direct structural price. -/
theorem native_word_price :
    Price NativeKidsRequest.structuralScale (fun r => r.word.length) :=
  Price.of_le (by intro r; unfold NativeKidsRequest.structuralScale NativeKidsRequest.originalSourceScale; omega)

/-- `prop:time`, paper/paper.tex: the
actual target field width has a direct structural price. -/
theorem native_width_price :
    Price NativeKidsRequest.structuralScale NativeKidsRequest.outputWidth :=
  Price.of_le (by intro r; unfold NativeKidsRequest.structuralScale; omega)

/-- `prop:time`, paper/paper.tex: each
original occurrence counter is bounded by the actual quartic census. -/
theorem native_occurrence_price : Price NativeKidsRequest.structuralScale
    (fun r => (r.toRowContext.originalIndex r.atom).val) := by
  have hn := native_arity_price
  have h : Price NativeKidsRequest.structuralScale (fun r => 2 * r.header.call.n ^ 4) := by
    price_with structuralScale_pos
  apply h.mono
  intro r
  exact (r.toRowContext.originalIndex r.atom).isLt.le.trans (original_count_bound r.toRowContext)

/-- `prop:time`, paper/paper.tex: the
actual first bank size is bounded by the same original quartic census. -/
theorem native_first_count_price : Price NativeKidsRequest.structuralScale
    (fun r => r.header.call.first.gates.length) := by
  have hn := native_arity_price
  have h : Price NativeKidsRequest.structuralScale (fun r => 2 * r.header.call.n ^ 4) := by
    price_with structuralScale_pos
  apply h.mono
  intro r
  have hg := original_count_bound r.toRowContext
  simp only [Builder.allGates, List.length_append] at hg
  omega

/-- `prop:time`, paper/paper.tex: an
actual natural codec costs only its bit length, with a safe linear
bound in the small original occurrence or count it encodes. -/
theorem native_nat_price {f : NativeKidsRequest → ℕ}
    (hf : Price NativeKidsRequest.structuralScale f) :
    Price NativeKidsRequest.structuralScale (fun r => (natWord (f r)).length) := by
  have h : Price NativeKidsRequest.structuralScale (fun r => 2 * (f r + 1) + 1) := by
    price_with structuralScale_pos
  exact h.mono fun r => by
    rw [NearCubicGates.Close.CounterAsm.natWord_len]
    have hn := NearCubicGates.Close.Dispatch.natBitLength_le_succ (f r)
    omega

/-- `prop:time`, paper/paper.tex: the
complete original call is a literal framed subfield of the actual source. -/
theorem native_call_price : Price NativeKidsRequest.structuralScale
    (fun r => (callWord r.header.call).length) :=
  native_word_price.mono fun r => call_length r

/-- `prop:time`, paper/paper.tex: all
actual affine-header bytes have a fixed original-arity polynomial bound. -/
theorem native_header_price : Price NativeKidsRequest.structuralScale
    (fun r => (r.toRowContext.rowHeader r.atom).length) := by
  have hn := native_arity_price
  have h : Price NativeKidsRequest.structuralScale (fun r => 1000 * (r.header.call.n + 1)^4) := by
    price_with structuralScale_pos
  exact h.mono fun r => header_length r.toRowContext r.atom

/-- `prop:time`, paper/paper.tex: the
actual role payload contains just its computed occurrence and affine
header, both already bounded in the original source resource. -/
theorem native_role_payload_price : Price NativeKidsRequest.structuralScale
    (fun r => r.rolePayload.length) := by
  have hi := native_nat_price native_occurrence_price
  have hh := native_header_price
  simp only [NativeKidsRequest.rolePayload, List.length_append]
  price_with structuralScale_pos

/-- `prop:time`, paper/paper.tex: actual
acquired source length is polynomial in original source resources. -/
theorem native_acquired_price : Price NativeKidsRequest.structuralScale
    (fun r => r.acquiredWord.length) := by
  have hw := native_word_price
  have hr := native_role_payload_price
  simp only [acquired_word_length]
  price_with structuralScale_pos

end NearQuarticWires.StageNativeKids
