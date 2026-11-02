import Proof.Quartic.StageModularCuts.Rows
import Proof.Quartic.StageModularCuts.Ready

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: canonical modular
coefficients retain each signed field's fixed-width encoding length. -/
theorem reduced_stream_length (p q : ℕ) (cuts : List MatrixScoreBatch.Cut) :
    ((cuts.map (StageRecovery.reduceCut q)).flatMap (MatrixScoreBatch.cutWord p)).length =
      (cuts.flatMap (MatrixScoreBatch.cutWord p)).length := by
  induction cuts with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.flatMap_cons, List.length_append, ih,
      cutWord_length, StageRecovery.reduceCut]

/-- `lem:print`, paper/paper.tex: the actual row
stream is followed by one terminating bit for its outer frame. -/
def streamProgram : Program := .seq rowsProgram (.wm (emitC 14 6 false))

def streamCost (r : Setup.Request) : ℕ :=
  r.cuts.length * (rowCost r.fieldWidth r.width + 2) + 9

/-- `lem:print` and `prop:time`, paper/paper.tex: from the literal bounded setup state, the physical stream
printer writes exactly the framed coefficient-reduced cut list. -/
theorem streamProgram_spec (r : Setup.Request) :
    ∃ b, WXExec (Setup.capacity r) streamProgram (Setup.ready r) b (streamCost r) ∧
      b.st 14 = r.output := by
  obtain ⟨hsourceCap, houtCap, hcountCap⟩ := setup_stream_capacity r
  obtain ⟨b, erows, _, hf⟩ := rowsProgram_spec (Setup.capacity r) r.fieldWidth r.modulus r.width
    r.cuts [] (Setup.ready r) (ready_workspace r) (by have h := r.modulus_two; omega) r.modulus_fit
    (fun c hc => ⟨(r.lengths c hc).1, (r.lengths c hc).2, (r.fits c hc).2.2⟩)
    rfl rfl rfl rfl rfl rfl rfl rfl
    (by change 0 + r.stream.length + 1 ≤ Setup.capacity r; omega)
    (by change 0 + 2 * r.stream.length + 1 ≤ Setup.capacity r; omega)
    hcountCap
  let out := (r.cuts.map (StageRecovery.reduceCut r.modulus)).flatMap (MatrixScoreBatch.cutWord r.fieldWidth)
  have hout : b.st 14 = marks out := by
    have he : (Setup.ready r).st 14 = [] := rfl
    rw [hf.output, he, List.nil_append]
  have hhead : b.sh 14 = (b.st 14).length := by
    rw [hf.outputHead, hout, show (Setup.ready r).sh 14 = 0 from rfl, Nat.zero_add]
  have hOP : b.val 6 = 2 * r.stream.length := by
    rw [hf.outputCount, Streaming.marks_length, reduced_stream_length,
      show (Setup.ready r).val 6 = 0 from rfl, Nat.zero_add]
    rfl
  have el := NearCubicGates.Close.Codec.emitBit_spec (Setup.capacity r)
    (14 : Fin 16) 6 false b hhead (by rw [hOP]; exact houtCap)
  refine ⟨appendO b 14 6 [false], (WXExec.seq erows (WXExec.wm el)).mono (by rfl), ?_⟩
  simp only [appendO_st, Function.update_self, hout]
  exact (NearCubicGates.Close.Codec.frame_eq_marks out).symm

end NearQuarticWires.StageModularCuts
