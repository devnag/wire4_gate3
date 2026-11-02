import Proof.Quartic.StageLift.FiniteCopy
import Proof.Quartic.StageMain.CallSkipTagged
import Proof.Quartic.StageRecovery.InputReturn

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain.CallSkip

/-- `lem:print`, paper/paper.tex: the finite
original call is retained separately from the possibly long Gamma table. -/
def callStore : Fin MM := 5

/-- `lem:print`, paper/paper.tex: use the actual
measured length to rewind and copy the finite original source once. -/
def retainMeasuredCall : St VV MM :=
  .seq (.op (.copy StageRecovery.tokenLengthVar lengthCounter))
    (.seq StageRecovery.inputReturnProgram (copyFiniteInput callStore))

/-- `lem:print`, paper/paper.tex: every backwards
step and finite source-bit copy is paid; the input cursor returns to
its original endpoint and no following suffix is scanned or duplicated. -/
theorem retainMeasuredCall_spec (C : Ctx) (bits rest : List Bool) (base : ℕ)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop base = bits ++ rest) (hip : a.ip = base + bits.length)
    (hlen : a.env lengthCounter = bits.length) (hfit : bits.length < 2 ^ C.Wd)
    (hempty : a.ram callStore = [] ∧ a.rc callStore = 0) :
    Hs C retainMeasuredCall a (12 * bits.length + 11) (fun b =>
      b.ip = a.ip ∧ b.ram callStore = bits.map Bool.toNat ∧
      b.rc callStore = bits.length ∧
      (∀ store, store ≠ callStore → b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [StageRecovery.tokenLengthVar, StageRecovery.inputReturnIndex, c0, t0]) := by
  unfold retainMeasuredCall
  refine (Hs.seq (t1 := 1) (t2 := 12 * bits.length + 9)
    (hs_copy C StageRecovery.tokenLengthVar lengthCounter a (by decide))
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let a' := a.set StageRecovery.tokenLengthVar (a.env lengthCounter)
  have hcf : Fr a a' [StageRecovery.tokenLengthVar] := Fr.set a _ (by simp)
  have hc' := Cst.of_fr hc hcf (by decide)
  refine (Hs.seq (t1 := 5 * bits.length + 4) (t2 := 7 * bits.length + 4)
    (StageRecovery.inputReturnProgram_spec C a' bits.length base
      (by simpa [a'] using hlen) hip hfit) fun b ⟨hbi, hbr, hbf⟩ => ?_).mono
      (by omega) (fun _ h => h)
  have hbrest : (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
      (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) := hbr
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.1) hbrest
  have hbrc : b.rc = a.rc := congrArg (fun t => t.2.2.1) hbrest
  have hbc := Cst.of_fr hc' hbf (by decide)
  have hblen : b.env lengthCounter = bits.length := by
    rw [hbf _ (by decide)]
    simpa (config := {decide := true}) [a', DS.set] using hlen
  refine (copyFiniteInput_spec C callStore bits rest b hbc (by rw [hbi]; exact hin)
    hblen hfit (by rw [hbrc, hbram, hempty.1, hempty.2]; rfl)).mono le_rfl ?_
  rintro d ⟨hdi, hdr, hdrc, hdo, hdsh, hdc, hdf⟩
  refine ⟨by rw [hdi, hbi, hip], ?_, ?_, ?_, ?_, hdc, ?_⟩
  · rw [hdr, hbram, hempty.1]
    rfl
  · rw [hdrc, hbrc, hempty.2]
    omega
  · intro store hs
    simpa only [hbram, hbrc] using hdo store hs
  · have hsmall : (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) := by
      exact congrArg (fun t => (t.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hbrest
    exact hdsh.trans hsmall
  · exact (hcf.weaken (by simp)).trans
      ((hbf.weaken (by simp)).trans (hdf.weaken (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)))

end NearQuarticWires.StageLift
