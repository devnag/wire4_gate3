import Proof.Quartic.StageLift.CallRetain

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain.CallSkip

/-- `lem:print`, paper/paper.tex: locate the true
finite original call from the tagged source and retain its bytes once. -/
def readCallSource : St VV MM := .seq scanTaggedCall retainMeasuredCall

/-- `lem:print`, paper/paper.tex: the original
call is physically acquired from the literal stage input. Its length
comes from the measured call scanner, and the arbitrary following
parameter, witness and Gamma suffix is preserved without being read. -/
theorem readCallSource_spec (C : Ctx) (c : Call) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = true :: (callWord c ++ rest))
    (hwidth : (callWord c).length + 2 ≤ C.Wd)
    (hempty : a.ram callStore = [] ∧ a.rc callStore = 0) :
    Hs C readCallSource a
      (3000 * ((callWord c).length + 1) ^ 3 + 12 * (callWord c).length + 16) (fun b =>
      b.ip = a.ip + 1 + (callWord c).length ∧
      b.env lengthCounter = (callWord c).length ∧
      b.ram callStore = (callWord c).map Bool.toNat ∧ b.rc callStore = (callWord c).length ∧
      (∀ store, store ≠ callStore → b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (gateListScratch ++
        [StageRecovery.tokenLengthVar, StageRecovery.inputReturnIndex, c0, t0])) := by
  unfold readCallSource
  refine (Hs.seq (t1 := 3000 * ((callWord c).length + 1) ^ 3 + 4)
    (t2 := 12 * (callWord c).length + 11)
    (scanTaggedCall_run C c rest a hc hin hwidth)
    fun b ⟨hbi, hbl, hbrest, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hinput : C.inp.drop (a.ip + 1) = callWord c ++ rest := by
    rw [← List.drop_drop, hin]
    rfl
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.1) hbrest
  have hbrc : b.rc = a.rc := congrArg (fun t => t.2.2.1) hbrest
  have hfit : (callWord c).length < 2 ^ C.Wd :=
    lt_trans (by omega) Nat.lt_two_pow_self
  refine (retainMeasuredCall_spec C (callWord c) rest (a.ip + 1) b hbc hinput hbi hbl hfit
    (by rw [hbram, hbrc]; exact hempty)).mono le_rfl ?_
  rintro d ⟨hdi, hdr, hdrc, hdo, hdsh, hdc, hdf⟩
  refine ⟨hdi.trans hbi, ?_, hdr, hdrc, ?_, ?_, hdc, ?_⟩
  · rw [hdf lengthCounter (by decide), hbl]
  · intro store hs
    simpa only [hbram, hbrc] using hdo store hs
  · have hsmall : (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) :=
      congrArg (fun t => (t.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hbrest
    exact hdsh.trans hsmall
  · exact (hbf.weaken (fun _ hx => List.mem_append_left _ hx)).trans
      (hdf.weaken (fun _ hx => List.mem_append_right _ hx))

end NearQuarticWires.StageLift
