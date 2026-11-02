import Proof.Quartic.StageCert.MomentSourcePrice
import Proof.Quartic.StageCert.MomentSyntaxScale
import Proof.Quartic.StageFormulaMetadata.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open Cells.ParameterArithmetic

/-- `lem:print` and `prop:time`, paper/paper.tex: literal signed packet formatting follows the actual
cold expression source with its physical stream handoff charged. -/
noncomputable def MomentRequest.formattedBudget {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  4*r.sourceBudget+4*r.validPacket.budget+12

/-- `lem:print`, paper/paper.tex: one fixed
ordinary machine reads only the original prepared source and exact
test/term indices, then produces the shared six-field header followed
by the original signed Formula word. -/
noncomputable def momentFormattedWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) MomentRequest.word
      (fun r=>r.validPacket.output) MomentRequest.formattedBudget := by
  let g : WordFunction (MomentRequest B1 B2) (fun r=>r.packet.word)
      (fun r=>r.validPacket.output) (fun r=>r.validPacket.budget) :=
    ⟨StageFormulaMetadata.rawFormatterWordFunction.program,
      fun r=>StageFormulaMetadata.rawFormatterWordFunction.realizes r.validPacket⟩
  exact Program.WordFunction.pipe (momentSourceWordFunction B1 B2) g

/-- `lem:print` and `prop:time`, paper/paper.tex: raw packet length includes its actual index,
degree, arity and framing, retaining the full tuple factor. -/
theorem MomentRequest.packet_length_scale {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.packet.word.length+1≤1000000*r.runtimeScale^4*
      ((Builder.allGates r.call).length+1)^r.selected.1.Xmax := by
  let S := r.runtimeScale
  let P := ((Builder.allGates r.call).length+1)^r.selected.1.Xmax
  have hS : 1≤S := by have hh := r.runtimeScale_basic.1; omega
  have hP : 1≤P := Nat.pow_pos (Nat.succ_pos _)
  obtain ⟨_,hX,hk,_,hA⟩ := r.syntax_parameters
  have hI : natBitLength r.index.val≤5*S := r.index_bits.trans (by change r.selected.1.k≤S at hk; omega)
  have hD : natBitLength (16*r.selected.1.Xmax+8*r.selected.1.k)≤25*S := by
    have hh := NearCubicGates.Close.Cells.nbl_le_self (16*r.selected.1.Xmax+8*r.selected.1.k)
    change r.selected.1.k≤S at hk
    change r.selected.1.Xmax≤S at hX
    omega
  have hF : r.packet.payload.length≤
      (formulaWord ⟨17*(Builder.allGates r.call).length,r.formula⟩).length := by
    change ((toks r.formula).flatMap tokWord).length≤_
    simp only [formulaWord,NearCubicGates.Close.Interfaces.listWord,List.length_append]
    omega
  have hraw := r.raw_formula_source_scale
  change _≤100000*S^4*P at hraw
  have hpayload : r.packet.payload.length≤100000*S^4*P := by omega
  have hS4 : S≤S^4*P := (Nat.le_self_pow (by decide) _).trans (Nat.le_mul_of_pos_right _ hP)
  have h14 : 1≤S^4*P := Nat.mul_pos (Nat.pow_pos hS) hP
  have h0 : natBitLength 0=1 := by decide
  change r.atomBits≤S at hA
  simp only [StageFormulaMetadata.RawWalkPacket.word,List.length_append,frame_length,
    NearCubicGates.Close.Cells.natWord_length]
  change (2*natBitLength r.index.val+1)+(2*natBitLength (16*r.selected.1.Xmax+8*r.selected.1.k)+1)+
    (2*natBitLength 0+1)+(2*r.atomBits+1)+(2*r.packet.payload.length+1)+1≤1000000*S^4*P
  rw [h0]
  nlinarith only [hI,hD,hA,hpayload,hS4,h14]

private theorem fourth_packet_power (S P : ℕ) :
    1000000000000000*(1000000*S^4*P)^4=
      (1000000000000000*1000000^4)*S^16*P^4 := by ring

/-- `prop:time`, paper/paper.tex: the exact
formatter's quartic source-word cost is paid without converting
construction weight into a coefficient-width premise. -/
theorem MomentRequest.formatterBudget_scale {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.validPacket.budget≤(1000000000000000*1000000^4)*r.runtimeScale^16*
      (((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4 := by
  calc
    _≤1000000000000000*(r.packet.word.length+1)^4 :=
      StageFormulaMetadata.rawFormatter_budget_le r.validPacket
    _≤1000000000000000*(1000000*r.runtimeScale^4*
        ((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left r.packet_length_scale 4)
    _=_ := fourth_packet_power _ _

end NearQuarticWires.StageCert.Tokens
