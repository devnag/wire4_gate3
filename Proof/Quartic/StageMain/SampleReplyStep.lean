import Proof.Quartic.StageMain.SampleCall
import Proof.Gates.Cells.Arith
import Proof.Quartic.StageGamma.FixedRead

/-!
# Reading one field bit from the sampler reply

`imp:seed`, paper/paper.tex: the field value is represented
by its low-bit-first binary word. The main pass, reads
every marked payload bit and accumulates its exact binary value.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.SampleCells

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells
open StageGamma

def sampleValue : Fin VV := 95
def samplePower : Fin VV := 96
def sampleIndex : Fin VV := 97

def sampleReplyStepScratch : List (Fin VV) := [sampleValue, samplePower, t0, vJ]

def sampleReplyScratch : List (Fin VV) := sampleIndex :: sampleReplyStepScratch

theorem readReplyBit_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (hread : a.kc < a.kout.length) :
    Hs C (.op (.rdK t0)) a 1 (fun b =>
      b.env t0 = bitOf a.kout a.kc ∧ b.kc = a.kc + 1 ∧ ReplyFrame a b ∧
      Cst b ∧ Fr a b [t0]) := by
  refine (hs_rdK C t0 a hread).mono le_rfl ?_
  rintro b rfl
  exact ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩,
    fun y hy => DS.set_env_ne _ _ (fun h => hy (by simp [h]))⟩

def addSampleBit : St VV MM :=
  .ite (.eq t0 v1) (.op (.add sampleValue samplePower)) skipS

theorem addSampleBit_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (bit : Bool) (hbit : a.env t0 = bit.toNat)
    (hfit : a.env sampleValue + a.env samplePower < 2 ^ C.Wd) :
    Hs C addSampleBit a 2 (fun b =>
      b.env sampleValue = a.env sampleValue + bit.toNat * a.env samplePower ∧
      Same a b ∧ Cst b ∧ Fr a b [sampleValue, vJ]) := by
  refine Hs.ite (c := .eq t0 v1) (show t0 ≠ v1 by decide) ?_ ?_
  · intro he
    have ht : bit = true := by
      revert he
      simp only [Cnd.eval, hbit, hc.one]
      cases bit <;> simp
    refine (hs_add C sampleValue samplePower a (by decide) hfit).mono le_rfl ?_
    rintro b rfl
    exact ⟨by simp [ht], Same.set _ _ _,
      Cst.of_fr hc (Fr.set a _ (by simp : sampleValue ∈ [sampleValue, vJ])) (by decide),
      Fr.set a _ (by simp)⟩
  · intro he
    have ht : bit = false := by
      revert he
      simp only [Cnd.eval, hbit, hc.one]
      cases bit <;> simp
    refine (skip_spec a).mono le_rfl ?_
    rintro b rfl
    exact ⟨by simp [ht, DS.set_env_ne _ _ (by decide : sampleValue ≠ vJ)], Same.set _ _ _,
      Cst.of_fr hc (Fr.set a _ (by simp : vJ ∈ [sampleValue, vJ])) (by decide),
      Fr.set a _ (by simp)⟩

def sampleReplyStep : St VV MM :=
  .seq (.op (.rdK t0)) (.seq (.op (.rdK t0))
    (.seq addSampleBit (.op (.shl samplePower))))

theorem sampleReplyStep_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (N v k : ℕ) (hk : k < N) (hW : N + 2 ≤ C.Wd)
    (ho : a.kout = frame (binary N v)) (hcursor : a.kc = 2 * k)
    (hv : a.env sampleValue = v % 2 ^ k) (hp : a.env samplePower = 2 ^ k) :
    Hs C sampleReplyStep a 8 (fun b =>
      b.env sampleValue = v % 2 ^ (k + 1) ∧ b.env samplePower = 2 ^ (k + 1) ∧
      b.kc = 2 * (k + 1) ∧ ReplyFrame a b ∧ Cst b ∧
      Fr a b sampleReplyStepScratch) := by
  have hlen : a.kout.length = 2 * N + 1 := by rw [ho, frame_length]; simp
  refine Hs.seq (t1 := 1) (t2 := 6)
    (readReplyBit_run C a hc (by omega)) ?_
  intro b ⟨_, hbkc, hfb, hbc, hfrb⟩
  refine Hs.seq (t1 := 1) (t2 := 4)
    (readReplyBit_run C b hbc (by rw [hfb.kout, hlen]; omega)) ?_
  intro d ⟨hdt, hdkc, hfd, hdc, hfrd⟩
  have hdf := hfb.trans hfd
  have hfr : Fr a d [t0] := hfrb.trans hfrd
  have hdv : d.env sampleValue = v % 2 ^ k := (hfr _ (by decide)).trans hv
  have hdp : d.env samplePower = 2 ^ k := (hfr _ (by decide)).trans hp
  have hbit : d.env t0 = (v.testBit k).toNat := by
    rw [hdt, hfb.kout, ho, hbkc, hcursor]
    unfold bitOf
    rw [frame_getD_odd, binary_getD N v k hk]
  have hpow : 2 ^ (k + 1) < 2 ^ C.Wd := Nat.pow_lt_pow_right (by decide) (by omega)
  have hsum : d.env sampleValue + d.env samplePower < 2 ^ C.Wd := by
    rw [hdv, hdp]
    have hm := Nat.mod_lt v (Nat.two_pow_pos k)
    have ht : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    omega
  refine Hs.seq (t1 := 2) (t2 := 1)
    (addSampleBit_run C d hdc (v.testBit k) hbit hsum) ?_
  intro e ⟨hev, hsame, hec, hefr⟩
  have hep : e.env samplePower = 2 ^ k := (hefr _ (by decide)).trans hdp
  refine (hs_shl C samplePower e (by rw [hep]; simpa [pow_succ, Nat.mul_comm] using hpow)).mono le_rfl ?_
  rintro f rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide : sampleValue ≠ samplePower), hev, hdv, hdp]
    exact (mod_two_pow_next v k).symm
  · simp [hep, pow_succ, Nat.mul_comm]
  · change e.kc = _
    rw [hsame.kc, hdkc, hbkc, hcursor]
    omega
  · exact hdf.trans ((show ReplyFrame d e from
      ⟨hsame.ip, hsame.out, hsame.ram, hsame.rc, hsame.kin, hsame.kout⟩).trans (ReplyFrame.set _ _ _))
  · exact Cst.of_fr hec (Fr.set e _ (by simp [sampleReplyStepScratch] : samplePower ∈ sampleReplyStepScratch)) (by decide)
  · exact ((hfr.weaken (by decide)).trans (hefr.weaken (by decide))).trans
      (Fr.set e _ (by simp [sampleReplyStepScratch]))

end NearQuarticWires.StageMain.SampleCells
