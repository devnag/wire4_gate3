import Proof.Quartic.StageCertificateControl.TestFold
import Proof.Quartic.StageCertTests.FlagOutput

/-!
# Emit the sole final original-center prefix

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageRecovery (countVar)

/-- The final original-center census of `sec:algorithm`,
paper/paper.tex, is retained through every full-size test. -/
def keepVar : Fin VV := ⟨123,by decide⟩

/-- Step 2 of `sec:algorithm`, paper/paper.tex:
select the actual final array, rewind it once, and emit only the
original-center prefix after all complete signed tests have finished. -/
def cropFold (first second : Fin MM) : St VV MM :=
  .seq (.op (.copy countVar keepVar))
    (.ite (.eq modeVar vZ)
      (.seq (.op (.rwM first)) (StageCertTests.emitFlagPrefix first))
      (.seq (.op (.rwM second)) (StageCertTests.emitFlagPrefix second)))

/-- The sole final crop of `sec:algorithm` and `prop:time`,
paper/paper.tex, reads the active
bitmap from its actual sequential store and pays the whole rewind. -/
theorem cropFold_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (first second : Fin MM) (mode : Bool) (hmode : a.env modeVar=mode.toNat)
    (flags : List Bool) (keep : ℕ) (hkeep : keep≤flags.length)
    (hk : a.env keepVar=keep) (hkfit : keep<2^C.Wd)
    (hflags : a.ram (activeStore first second mode)=flags.map Bool.toNat)
    (hcursor : a.rc (activeStore first second mode)=flags.length) :
    Hs C (cropFold first second) a (flags.length+10*keep+11) (fun b =>
      b.out=a.out++frame (flags.take keep) ∧ Cst b) := by
  unfold cropFold
  refine (Hs.seq (t2 := flags.length+10*keep+9)
    (hs_copy C countVar keepVar a (by decide)) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let start := a.set countVar (a.env keepVar)
  have hstart : Cst start := Cst.of_fr (T := [countVar]) hc
    (Fr.set _ _ (by decide)) (by decide)
  cases mode with
  | false =>
    simp only [activeStore,Bool.false_eq_true,ite_false,ite_true] at hflags hcursor
    refine Hs.iteT (show modeVar≠vZ by decide)
      (by simp (config := {decide := true}) [Cnd.eval,start,DS.set,hmode,hc.z]) ?_
    have hr : Hs C (.op (.rwM first)) start (flags.length+1) (·=start.rew first) := by
      simpa only [start,DS.set_rc,hcursor] using hs_rwM C first start
    refine (Hs.seq (t2 := 10*keep+6) hr fun b hb => ?_).mono (by omega) (fun _ h => h)
    subst b
    refine (StageCertTests.emitFlagPrefix_spec C (start.rew first)
      ⟨hstart.z,hstart.one,hstart.two⟩ first flags keep hkeep hflags
      (by simp [DS.rew]) (by simp [start,DS.rew,DS.set,hk]) hkfit).mono le_rfl ?_
    rintro b ⟨hbo,_,_,hbc⟩
    exact ⟨hbo,hbc⟩
  | true =>
    simp only [activeStore,Bool.false_eq_true,ite_false,ite_true] at hflags hcursor
    refine Hs.iteF (show modeVar≠vZ by decide)
      (by simp (config := {decide := true}) [Cnd.eval,start,DS.set,hmode,hc.z]) ?_
    have hr : Hs C (.op (.rwM second)) start (flags.length+1) (·=start.rew second) := by
      simpa only [start,DS.set_rc,hcursor] using hs_rwM C second start
    refine (Hs.seq (t2 := 10*keep+6) hr fun b hb => ?_).mono (by omega) (fun _ h => h)
    subst b
    refine (StageCertTests.emitFlagPrefix_spec C (start.rew second)
      ⟨hstart.z,hstart.one,hstart.two⟩ second flags keep hkeep hflags
      (by simp [DS.rew]) (by simp [start,DS.rew,DS.set,hk]) hkfit).mono le_rfl ?_
    rintro b ⟨hbo,_,_,hbc⟩
    exact ⟨hbo,hbc⟩

end NearQuarticWires.StageCertificateControl
