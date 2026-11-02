import Proof.Quartic.StageMain.SampleReplyStep

/-!
# The exact sampler reply decoder

`imp:seed`, paper/paper.tex, and the main pass: the field word is decoded by a counted binary loop.
It consumes every marker and the final delimiter and retains the
original input, stored seed coefficients and cached modulus.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.SampleCells

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells
open StageGamma

def readSampleReply : St VV MM :=
  .seq (.op (.zero sampleValue)) (.seq (.op (.copy samplePower v1))
    (.seq (forS sampleIndex ell sampleReplyStep) (.op (.rdK t0))))

theorem readSampleReply_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (N v : ℕ) (he : a.env ell = N) (hW : N + 2 ≤ C.Wd) (hv : v < 2 ^ N)
    (ho : a.kout = frame (binary N v)) (hcursor : a.kc = 0) :
    Hs C readSampleReply a (12 * N + 10) (fun b =>
      b.env sampleValue = v ∧ b.kc = 2 * N + 1 ∧ ReplyFrame a b ∧ Cst b ∧
      Fr a b sampleReplyScratch) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env sampleValue = v % 2 ^ k ∧ b.env samplePower = 2 ^ k ∧
    b.kc = 2 * k ∧ ReplyFrame a b ∧ Cst b ∧ Fr a b sampleReplyScratch
  have hI : ∀ k b x, I k b → I k (b.set sampleIndex x) := by
    intro k b x ⟨hb, hp, hk, hf, hbc, hfr⟩
    exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hb,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hp, hk,
      hf.trans (ReplyFrame.set _ _ _),
      Cst.of_fr hbc (Fr.set b x (by simp [sampleReplyScratch, sampleReplyStepScratch] : sampleIndex ∈ sampleReplyScratch))
        (by decide), hfr.trans (Fr.set b x (by simp [sampleReplyScratch, sampleReplyStepScratch]))⟩
  have hfit : N < 2 ^ C.Wd := (show N < C.Wd by omega).trans Nat.lt_two_pow_self
  have hloop : ∀ b, I 0 b → b.env ell = N →
      Hs C (forS sampleIndex ell sampleReplyStep) b (12 * N + 4)
        (fun d => I N d) := by
    intro b hb hbe
    refine (forS_spec' (C := C) sampleIndex ell (by decide) sampleReplyStep b N hfit I 8
      hI hb hbe ?_).mono (by omega) (fun _ h => h.1)
    intro k hk d ⟨hdv, hdp, hdk, hdf, hdc, hdfr⟩ hdi hde
    refine (sampleReplyStep_run C d hdc N v k hk hW (hdf.kout.trans ho) hdk hdv hdp).mono le_rfl ?_
    intro e ⟨hev, hep, hek, hef, hec, hefr⟩
    exact ⟨⟨hev, hep, hek, hdf.trans hef, hec, hdfr.trans (hefr.weaken (by simp [sampleReplyScratch, sampleReplyStepScratch]))⟩,
      (hefr sampleIndex (by decide)).trans hdi,
      (hefr ell (by decide)).trans hde⟩
  unfold readSampleReply
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1 + ((12 * N + 4) + 1 + 1) + 1)
    (hs_zero C sampleValue a) ?_) (by omega) (fun _ h => h)
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := (12 * N + 4) + 1 + 1) (hs_copy C samplePower v1 _ (by decide)) ?_
  rintro d rfl
  let d := (a.set sampleValue 0).set samplePower ((a.set sampleValue 0).env v1)
  have hfrd : Fr a d sampleReplyScratch :=
    (Fr.set a _ (by simp [sampleReplyScratch, sampleReplyStepScratch])).trans (Fr.set _ _ (by simp [sampleReplyScratch, sampleReplyStepScratch]))
  have hdc : Cst d := Cst.of_fr hc hfrd (by decide)
  have hd : I 0 d := by
    refine ⟨?_, ?_, hcursor, ?_, hdc, hfrd⟩
    · simp [d, sampleValue, samplePower, Nat.mod_one]
    · simp [d, hc.one, DS.set_env_ne _ _ (by decide : v1 ≠ sampleValue)]
    · exact (ReplyFrame.set _ _ _).trans (ReplyFrame.set _ _ _)
  refine Hs.seq (t1 := 12 * N + 4) (t2 := 1)
    (hloop d hd ((hfrd ell (by decide)).trans he)) ?_
  intro e ⟨hev, _, hek, hef, hec, hefr⟩
  refine (readReplyBit_run C e hec (by rw [hek, hef.kout, ho, frame_length]; simp)).mono le_rfl ?_
  intro f ⟨_, hfk, hff, hfc, hffr⟩
  exact ⟨(hffr sampleValue (by decide)).trans (hev.trans (Nat.mod_eq_of_lt hv)),
    hfk.trans (by rw [hek]), hef.trans hff, hfc,
    hefr.trans (hffr.weaken (by simp [sampleReplyScratch, sampleReplyStepScratch]))⟩

end NearQuarticWires.StageMain.SampleCells
