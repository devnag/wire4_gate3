import Proof.Quartic.StageMainPopulation.State
import Proof.Quartic.StageMainPopulation.Prefix

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageMainMask StageCert

/-- `def:mask`, witness (W2) and `prop:time`, paper/paper.tex: traverse the actual second original
bank with the continuing witness index and exact first-bank total. -/
theorem secondBank_run (C : Ctx) (a : DS VV) (r : PopulationRequest)
    (hc : Cst a) (hr : Retained a r) (hcp : a.cp = pos2 r.call)
    (hi : a.env sourceWitnessIndex = r.offset + r.call.first.gates.length)
    (ht : a.env populationTotal = firstValue r)
    (hin : C.cw = r.word) (hW : 2 * C.cw.length + 8 ≤ C.Wd) :
    Hs C populationList a
      (r.call.second.gates.length * (900 * (C.cw.length + 2)^2 + 106) +
        30 * natBitLength r.call.second.gates.length + 37) (fun b =>
      b.env populationTotal = r.value ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b) := by
  have hcount := counts_le r
  rw [← hin] at hcount
  have hsmall := Nat.lt_two_pow_self (n := C.Wd)
  have hbits := r.selection_fits
  have hfirst := firstValue_le r
  have hpoints : ∀ l, a.env (cornerPoint l) < 2 ^ C.Wd := by
    intro l
    rw [hr.corners]
    have h := corner_bitLength r l
    rw [← hin] at h
    exact (lt_natBitLength _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hread := populationList_run C r.call.second.gates a hc (secondListRest r)
    (witnessPrefix r) r.witness [] (r.offset + r.call.first.gates.length)
    (by rw [hcp, hin]; exact secondList_input r) (by omega) hpoints hbits
    hr.witnessBase hi (by rw [hin, request_word, List.append_nil])
    (by rw [ht]; omega) (by omega)
  refine hread.mono le_rfl ?_
  rintro b ⟨hbtotal, _, _, _, _, hbwq, hbout, hbc, _⟩
  have hp : (fun l => a.env (cornerPoint l)) = r.corners := funext hr.corners
  have hvalue : r.value = firstValue r + populationPrefix r.call.second.gates r.corners
      r.witness (r.offset + r.call.first.gates.length) r.call.second.gates.length :=
    populationPrefix_append _ _ _ _ _
  exact ⟨by rw [ht, hp] at hbtotal; exact hbtotal.trans hvalue.symm, hbwq, hbout, hbc⟩

end NearQuarticWires.StageMainPopulation
