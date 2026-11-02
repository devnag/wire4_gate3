import Proof.Quartic.StageMain.CompactFrame
import Proof.Quartic.StageLift.PreparedPrefix

/-!
# Acquiring the finite preparation word for all samples

`sec:algorithm`, paper/paper.tex:
the call, parameters and framed witness are read from the original
source and retained once. Every later certificate or seed bit remains
in the source suffix; the runtime retained length counts only this
finite preparation word.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Compact

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageLift CallSkip

def compactLength : Fin VV := 114

def compactInput (c : Call) (p : Cells.Parameters) (witness : List Bool) : List Bool :=
  preparedPrefixWord c p ++ frame witness

def acquireCompact : St VV MM := .seq scanPreparedPrefix
  (.seq retainMeasuredPrefix (.seq copyWitnessFrame (.op (.copy compactLength lengthCounter))))

def acquireScratch : List (Fin VV) := gateListScratch ++
  [StageRecovery.tokenLengthVar, StageRecovery.inputReturnIndex, c0, t0] ++
  frameScratch ++ [compactLength]

def acquireCost (c : Call) (p : Cells.Parameters) (witness : List Bool) : ℕ :=
  3000 * ((callWord c).length + 1) ^ 3 +
  4000 * ((Program.parametersWord p).length + 1) ^ 2 +
  12 * (preparedPrefixWord c p).length + 11 * witness.length + 40

theorem acquireCompact_run (C : Ctx) (c : Call) (p : Cells.Parameters)
    (witness rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = compactInput c p witness ++ rest)
    (hW : (preparedPrefixWord c p).length + 2 ≤ C.Wd)
    (hcap : (compactInput c p witness).length < 2 ^ C.Wd)
    (hempty : a.ram compactStore = [] ∧ a.rc compactStore = 0) :
    Hs C acquireCompact a (acquireCost c p witness) (fun b =>
      b.ip = a.ip + (compactInput c p witness).length ∧
      b.env compactLength = (compactInput c p witness).length ∧
      b.env lengthCounter = (compactInput c p witness).length ∧
      b.ram compactStore = (compactInput c p witness).map Bool.toNat ∧
      b.rc compactStore = (compactInput c p witness).length ∧
      (∀ store, store ≠ compactStore → b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b acquireScratch) := by
  have hinput : C.inp.drop a.ip = preparedPrefixWord c p ++ (frame witness ++ rest) := by
    simpa only [compactInput, List.append_assoc] using hin
  unfold acquireCompact
  refine (Hs.seq (t2 := 12 * (preparedPrefixWord c p).length + 11 * witness.length + 23)
    (scanPreparedPrefix_spec C c p (frame witness ++ rest) a hc hinput hW) ?_).mono
    (by unfold acquireCost; omega) (fun _ h => h)
  rintro b ⟨hbip, hblen, hbrest, hbc, hbfr⟩
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.1) hbrest
  have hbrc : b.rc = a.rc := congrArg (fun t => t.2.2.1) hbrest
  refine (Hs.seq (t2 := 11 * witness.length + 10)
    (retainMeasuredPrefix_spec C (preparedPrefixWord c p) (frame witness ++ rest) a.ip b hbc
      hinput hbip hblen (by simp only [compactInput, List.length_append] at hcap; omega)
      (by rw [hbram, hbrc]; exact hempty)) ?_).mono (by omega) (fun _ h => h)
  rintro d ⟨hdip, hdr, hdrc, hdo, hdrest, hdc, hdfr⟩
  have hdlen : d.env lengthCounter = (preparedPrefixWord c p).length := by
    rw [hdfr _ (by decide), hblen]
  have hdinput : C.inp.drop d.ip = frame witness ++ rest := by
    rw [hdip, hbip, ← List.drop_drop, hinput, List.drop_left]
  refine (Hs.seq (t2 := 1)
    (copyWitnessFrame_run C witness rest d hdc hdinput
      (by rw [hdr, hdrc, List.length_map])
      (by rw [hdlen]; simpa only [compactInput, List.length_append] using hcap)) ?_).mono
      (by omega) (fun _ h => h)
  rintro e ⟨heip, helen, her, herc, heo, herest, hec, hefr⟩
  have heleq : e.env lengthCounter = (compactInput c p witness).length := by
    rw [helen, hdlen]
    simp only [compactInput, List.length_append]
  refine (hs_copy C compactLength lengthCounter e (by decide)).mono le_rfl ?_
  rintro f rfl
  refine ⟨?_, by simpa using heleq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change e.ip = _
    rw [heip, hdip, hbip]
    simp only [compactInput, List.length_append]
    omega
  · rw [DS.set_env_ne _ _ (by decide)]
    exact heleq
  · change e.ram compactStore = _
    rw [her, hdr]
    simp only [compactInput, List.map_append]
  · change e.rc compactStore = _
    rw [herc, hdrc]
    simp only [compactInput, List.length_append]
  · intro store hs
    obtain ⟨heR, heC⟩ := heo store hs
    obtain ⟨hdR, hdC⟩ := hdo store hs
    exact ⟨heR.trans (hdR.trans (congrFun hbram store)), heC.trans (hdC.trans (congrFun hbrc store))⟩
  · have hsmall : (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) :=
      congrArg (fun t => (t.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hbrest
    exact herest.trans (hdrest.trans hsmall)
  · exact Cst.of_fr hec (Fr.set (T := [compactLength]) e _ (by simp)) (by decide)
  · exact (hbfr.weaken (by intro x hx; simp only [acquireScratch, List.mem_append]; tauto)).trans
      ((hdfr.weaken (by intro x hx; simp only [acquireScratch, List.mem_append]; tauto)).trans
        ((hefr.weaken (by intro x hx; simp only [acquireScratch, List.mem_append]; tauto)).trans
          (Fr.set e _ (by simp [acquireScratch]))))

end NearQuarticWires.StageMain.Compact
