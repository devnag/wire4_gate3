import Proof.Quartic.StageMainPopulation.State

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageMainMask StageCert

/-- `def:mask`, witness (W2) and `prop:time`, paper/paper.tex: traverse the actual first original
gate-list bytes and read every selected magnitude from the real witness. -/
theorem firstBank_run (C : Ctx) (a : DS VV) (r : PopulationRequest)
    (hc : Cst a) (hr : Retained a r) (hcp : a.cp = pos1 r.call)
    (hi : a.env sourceWitnessIndex = r.offset) (ht : a.env populationTotal = 0)
    (hin : C.cw = r.word) (hW : 2 * C.cw.length + 8 ≤ C.Wd) :
    Hs C populationList a
      (r.call.first.gates.length * (900 * (C.cw.length + 2)^2 + 106) +
        30 * natBitLength r.call.first.gates.length + 37) (fun b =>
      Retained b r ∧ b.env populationTotal = firstValue r ∧
      b.env sourceWitnessIndex = r.offset + r.call.first.gates.length ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b) := by
  have hcount := counts_le r
  rw [← hin] at hcount
  have hsmall := Nat.lt_two_pow_self (n := C.Wd)
  have hbits := r.selection_fits
  have hpoints : ∀ l, a.env (cornerPoint l) < 2 ^ C.Wd := by
    intro l
    rw [hr.corners]
    have h := corner_bitLength r l
    rw [← hin] at h
    exact (lt_natBitLength _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hread := populationList_run C r.call.first.gates a hc (firstListRest r)
    (witnessPrefix r) r.witness [] r.offset
    (by rw [hcp, hin]; exact firstList_input r) (by omega) hpoints (by omega)
    hr.witnessBase hi (by rw [hin, request_word, List.append_nil])
    (by rw [ht]; omega) (by omega)
  refine hread.mono le_rfl ?_
  rintro b ⟨hbtotal, hbindex, _, _, _, hbwq, hbout, hbc, hbf⟩
  have hp : (fun l => a.env (cornerPoint l)) = r.corners := funext hr.corners
  exact ⟨hr.frame hbf (by intro l; fin_cases l <;> decide) (by decide) (by decide),
    by simpa only [ht, hp, Nat.zero_add, firstValue] using hbtotal, hbindex, hbwq, hbout, hbc⟩

end NearQuarticWires.StageMainPopulation
