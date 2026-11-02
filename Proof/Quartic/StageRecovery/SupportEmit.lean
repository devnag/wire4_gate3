import Proof.Quartic.StageRecovery.SupportCodec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Expand

/-- `lem:print`, paper/paper.tex: the finite work
frame of one genuine support-index serialization step. -/
def supportEmitScratch : List (Fin VV) :=
  [supportWork, supportQuotient, supportBit, t3, t5, t6, t7, t8, t9, vJ]

/-- `lem:print`, paper/paper.tex: a support index is
emitted exactly when its next actual binary coordinate is present. -/
def supportEmitStep : St VV MM :=
  .seq supportHalfProgram
    (.ite (.eq supportBit v1) (emitVariable supportIndex) skipS)

/-- `lem:print`, paper/paper.tex: actual output
serialization preserves every source, record-store and call-stream head. -/
def supportPrintRest (a : DS VV MM) := (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc)

/-- `lem:print`, paper/paper.tex: one actual support
bit either emits the complete ordinary index codec or emits no bytes,
paying the binary natural-codec writer in the present branch. -/
theorem supportEmitStep_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (s k : ℕ) (hs : a.env supportWork = s / 2 ^ k)
    (hk : a.env supportIndex = k) (hW : 2 ≤ C.Wd)
    (hfit : natBitLength k + 2 < 2 ^ C.Wd) :
    Hs C supportEmitStep a (40 * natBitLength k + 47) (fun b =>
      b.env supportWork = s / 2 ^ (k + 1) ∧
      b.out = a.out ++ (if s.testBit k then natWord k else []) ∧
      supportPrintRest b = supportPrintRest a ∧ Cst b ∧ Fr a b supportEmitScratch) := by
  have hfour : 4 ≤ 2 ^ C.Wd := by
    exact (show 4 = 2 ^ 2 by norm_num).le.trans (Nat.pow_le_pow_right (by decide) hW)
  unfold supportEmitStep
  refine (Hs.seq (t2 := 40 * natBitLength k + 43)
    (supportHalfProgram_spec C a hc s k hs hfour)
    fun b ⟨hw, hb, hsh, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hsame := Same.of_sh hsh
  have hbk : b.env supportIndex = k := by rw [hbf _ (by decide), hk]
  refine (Hs.ite (c := .eq supportBit v1) (t := 40 * natBitLength k + 42)
    (show supportBit ≠ v1 by decide)
    (fun he => ?_) (fun he => ?_)).mono (by omega) (fun _ h => h)
  · have hbit : s.testBit k = true := by
      revert he
      simp only [Cnd.eval, hb, hbc.one]
      cases s.testBit k <;> simp
    refine (emitVariable_spec C b hbc supportIndex (by decide) hW
      (by rw [hbk]; exact hfit)).mono (by rw [hbk]) ?_
    rintro d ⟨hdo, hdr, hdc, hdf⟩
    refine ⟨?_, ?_, ?_, hdc,
      Fr.trans (Fr.weaken hbf (by decide)) (Fr.weaken hdf (by decide))⟩
    · rw [hdf _ (by decide), hw]
    · simp only [hdo, hsame.out, hbk, hbit, ite_true]
    · exact hdr.trans (by simp only [supportPrintRest, hsame.ip, hsame.ram, hsame.rc,
        hsame.kin, hsame.kout, hsame.kc])
  · have hbit : s.testBit k = false := by
      revert he
      simp only [Cnd.eval, hb, hbc.one]
      cases s.testBit k <;> simp
    refine (hs_zero C vJ b).mono (by omega) ?_
    rintro d rfl
    refine ⟨?_, ?_, ?_,
      Cst.of_fr (T := [vJ]) hbc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans (Fr.weaken hbf (by decide)) (Fr.set _ _ (by simp [supportEmitScratch]))⟩
    · simpa (config := {decide := true}) only [DS.set_env_ne] using hw
    · simpa only [DS.set, hbit, Bool.false_eq_true, if_false, List.append_nil] using hsame.out
    · simp only [supportPrintRest, DS.set, hsame.ip, hsame.ram, hsame.rc,
        hsame.kin, hsame.kout, hsame.kc]

/-- `lem:print`, paper/paper.tex: the complete
index pass scans every original atom coordinate in increasing order. -/
def emitSupportIndicesProgram : St VV MM :=
  .seq (.op (.copy supportWork supportVar)) (forS supportIndex arityVar supportEmitStep)

/-- `lem:print`, paper/paper.tex: the physical index
pass emits exactly the canonical sorted support indices, retaining all
other tapes and paying a polynomial arity factor per monomial. -/
theorem emitSupportIndicesProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (V s : ℕ) (hV : a.env arityVar = V) (hs : a.env supportVar = s)
    (hVfit : V + 3 < 2 ^ C.Wd) (hW : 2 ≤ C.Wd) :
    Hs C emitSupportIndicesProgram a (V * (40 * (V + 1) + 54) + 6) (fun b =>
      b.out = a.out ++ (supportIndices s V).flatMap natWord ∧
      supportPrintRest b = supportPrintRest a ∧ Cst b ∧
      Fr a b (supportIndex :: supportEmitScratch)) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env supportWork = s / 2 ^ k ∧
    b.out = a.out ++ (supportIndices s k).flatMap natWord ∧
    supportPrintRest b = supportPrintRest a ∧ Cst b ∧
      Fr a b (supportIndex :: supportEmitScratch)
  unfold emitSupportIndicesProgram
  refine (Hs.seq (t2 := V * (40 * (V + 1) + 54) + 4)
    (hs_copy C supportWork supportVar a (by decide)) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let start := a.set supportWork s
  have heq : a.set supportWork (a.env supportVar) = start := by rw [hs]
  rw [heq]
  have hstart : Fr a start (supportIndex :: supportEmitScratch) := Fr.set _ _ (by simp [supportEmitScratch])
  have hstartc : Cst start := Cst.of_fr hc hstart (by decide)
  refine (forS_spec' (C := C) supportIndex arityVar (by decide) supportEmitStep start V
    (by omega) I (40 * (V + 1) + 50) ?_
    ⟨by simp [start, DS.set], by simp [start, DS.set, supportIndices], rfl, hstartc, hstart⟩
    (by rw [hstart _ (by decide), hV]) ?_).mono le_rfl ?_
  · intro k b value ⟨hw, ho, hr, hbc, hbf⟩
    exact ⟨by simpa (config := {decide := true}) only [DS.set_env_ne] using hw,
      ho, hr, Cst.of_fr (T := [supportIndex]) hbc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans hbf (Fr.set _ _ (by simp))⟩
  · intro k hk b ⟨hw, ho, hr, hbc, hbf⟩ hbi hbn
    have hbitlen := nbl_le_self k
    refine (supportEmitStep_spec C b hbc s k hw hbi hW (by omega)).mono (by omega) ?_
    rintro d ⟨hdw, hdo, hdr, hdc, hdf⟩
    refine ⟨⟨hdw, ?_, hdr.trans hr, hdc,
      Fr.trans hbf (Fr.weaken hdf (by intro y hy; exact List.mem_cons_of_mem _ hy))⟩,
      by rw [hdf _ (by decide), hbi], by rw [hdf _ (by decide), hbn]⟩
    rw [hdo, ho, supportIndices_succ, List.flatMap_append, List.append_assoc]
    cases s.testBit k <;> simp
  · rintro b ⟨⟨_, ho, hr, hbc, hbf⟩, _, _⟩
    exact ⟨ho, hr, hbc, hbf⟩

end NearQuarticWires.StageRecovery
