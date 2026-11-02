import Proof.Quartic.StageCertificateControl.FoldAndCrop
import Proof.Quartic.StageCertTests.PrefixGeometry
import Proof.Quartic.StageCertTests.ScheduleFields
import Proof.Gates.Cells.Arith

/-!
# Actual original-center and native-square censuses

Paper: `imp:partition`, paper/paper.tex,
Step 2 of `sec:algorithm`, and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Shared (StarParams)
open NearCubicGates.Close.Cells
open StageRecovery (countVar widthVar)

/-- The actual original-center census of `imp:partition`,
paper/paper.tex. -/
def centerCount (n k : ℕ) : ℕ := 2^(n-k)

/-- The padded native-square census of `lem:print`,
paper/paper.tex. -/
def paddedCount (n k : ℕ) : ℕ := 2^(2*((n-k+1)/2))

/-- The balanced original split of `imp:partition`,
paper/paper.tex, determines the actual larger half. -/
theorem leftCenterBits_exact (P : StarParams) :
    P.leftCenterBits=(P.n-P.k+1)/2 := by
  have hs := P.centerBits_sum
  have hb := P.centerBits_balanced
  omega

/-- The physical native census of `lem:print`, paper/paper.tex, is computed from the actual original arity and
selected live dimension, without a supplied table-size oracle. -/
theorem paddedCount_exact (P : StarParams) :
    paddedCount P.n P.k=(2^P.leftCenterBits)^2 := by
  rw [leftCenterBits_exact]
  unfold paddedCount
  rw [←pow_mul,Nat.mul_comm]

/-- The exact native padding of `prop:time`, paper/paper.tex, costs at most twice the original-center census. -/
theorem paddedCount_le_two_centers (n k : ℕ) :
    paddedCount n k≤2*centerCount n k := by
  have he : 2*((n-k+1)/2)≤1+(n-k) := by omega
  calc
    paddedCount n k≤2^(1+(n-k)) := Nat.pow_le_pow_right (by decide) he
    _=2*centerCount n k := by simp [centerCount,pow_add]

/-- Step 2 of `sec:algorithm`, paper/paper.tex:
a scalar exponent register is separate from both native bitmap counts. -/
def censusExponentVar : Fin VV := ⟨124,by decide⟩

/-- The original-center power of two in `sec:algorithm`,
paper/paper.tex, uses a distinct arithmetic destination. -/
def censusPowerVar : Fin VV := ⟨125,by decide⟩

/-- The exact dimension arithmetic of `imp:partition` and
`sec:algorithm`, paper/paper.tex. -/
def censusDimensions : St VV MM :=
  .seq (.op (.copy keepVar widthVar))
    (.seq (.op (.sub keepVar (StageCertTests.ScheduleField.variable .k)))
      (.seq (.op (.copy censusExponentVar keepVar))
        (.seq (.op (.inc censusExponentVar))
          (.seq (.op (.half censusExponentVar)) (.op (.shl censusExponentVar))))))

/-- Step 2 of `sec:algorithm`, paper/paper.tex:
the two actual count powers are produced by the fixed arithmetic
program, without enumerating any native table entries. -/
def setBitmapCensuses : St VV MM :=
  .seq censusDimensions (.seq (powP v2 censusExponentVar countVar)
    (.seq (powP v2 keepVar censusPowerVar) (.op (.copy keepVar censusPowerVar))))

/-- The exact scalar dimension instructions of `sec:algorithm`,
paper/paper.tex, retain the original center exponent and
the even native-square exponent while preserving all source data. -/
theorem censusDimensions_spec (C : Ctx) (a : DS VV MM) (n k : ℕ)
    (hn : a.env widthVar=n) (hk : a.env (StageCertTests.ScheduleField.variable .k)=k)
    (hkn : k≤n) (hwidth : n+2≤C.Wd) :
    Hs C censusDimensions a 11 (fun b =>
      b.env keepVar=n-k ∧ b.env censusExponentVar=2*((n-k+1)/2) ∧
      b.sh=a.sh ∧ Fr a b [keepVar,censusExponentVar]) := by
  have hp : C.Wd<2^C.Wd := Nat.lt_two_pow_self
  unfold censusDimensions
  refine Hs.seq (t2 := 9) (hs_copy C keepVar widthVar a (by decide)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 7) (hs_sub C keepVar (StageCertTests.ScheduleField.variable .k)
    _ (by decide) (by simpa (config := {decide := true}) [DS.set,hn,hk] using hkn)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 5) (hs_copy C censusExponentVar keepVar _ (by decide)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 3) (hs_inc C censusExponentVar _ (by
    simp (config := {decide := true}) [DS.set,hn,hk]
    omega)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 1) (hs_half C censusExponentVar _) fun b hb => ?_
  subst b
  refine (hs_shl C censusExponentVar _ (by
    simp (config := {decide := true}) [DS.set,hn,hk]
    omega)).mono le_rfl ?_
  rintro b rfl
  refine ⟨?_,?_,rfl,?_⟩
  · simp (config := {decide := true}) [DS.set,hn,hk]
  · simp (config := {decide := true}) [DS.set,hn,hk]
  · exact Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide))
          (Fr.trans (Fr.set _ _ (by decide))
            (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))))

/-- The count construction in `sec:algorithm` and `prop:time`,
paper/paper.tex, computes both
actual native and original-center censuses in polynomial scalar time. -/
theorem setBitmapCensuses_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (n k : ℕ)
    (hn : a.env widthVar=n) (hk : a.env (StageCertTests.ScheduleField.variable .k)=k)
    (hkn : k≤n) (hwidth : n+2≤C.Wd) :
    Hs C (setBitmapCensuses) a (100*(n+1)) (fun b =>
      b.env countVar=paddedCount n k ∧ b.env keepVar=centerCount n k ∧
      b.sh=a.sh ∧ Cst b ∧ Fr a b [keepVar,censusExponentVar,countVar,censusPowerVar,a1,c4]) := by
  let E := 2*((n-k+1)/2)
  have hE : E≤n+1 := by dsimp [E];omega
  have hpow : 2^E<2^C.Wd := Nat.pow_lt_pow_right (by decide) (by omega)
  have hcenter : 2^(n-k)<2^C.Wd := Nat.pow_lt_pow_right (by decide) (by omega)
  have hsmall : C.Wd<2^C.Wd := Nat.lt_two_pow_self
  unfold setBitmapCensuses
  refine (Hs.seq (t2 := (7*E+8)+(7*(n-k)+8)+3)
    (censusDimensions_spec C a n k hn hk hkn hwidth)
    fun b ⟨hbk,hbe,hbs,hbf⟩ => ?_).mono (by dsimp [E];omega) (fun _ h => h)
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  have hp : Hs C (powP v2 censusExponentVar countVar) b (7*E+8)
      (fun d => d.env countVar=2^E ∧ d.sh=b.sh ∧ Fr b d [countVar,a1,c4]) := by
    refine (powP_spec v2 censusExponentVar countVar (by decide) b
      (by intro j hj;rw [hbc.two];exact (Nat.pow_le_pow_right (by decide) (by dsimp [E];omega)).trans_lt hpow)
      (by rw [hbe];dsimp [E] at hE ⊢;omega) (by omega)).mono ?_ ?_
    · rw [hbe]
      dsimp [E]
      omega
    · rintro d ⟨hd,hds,hdf⟩
      exact ⟨by simpa only [hbc.two,hbe] using hd,hds,hdf⟩
  refine Hs.seq (t2 := 7*(n-k)+10) hp fun d ⟨hdn,hds,hdf⟩ => ?_
  have hdc : Cst d := Cst.of_fr hbc hdf (by decide)
  have hdk : d.env keepVar=n-k := (hdf _ (by decide)).trans hbk
  have hp2 : Hs C (powP v2 keepVar censusPowerVar) d (7*(n-k)+8)
      (fun e => e.env censusPowerVar=2^(n-k) ∧ e.sh=d.sh ∧ Fr d e [censusPowerVar,a1,c4]) := by
    refine (powP_spec v2 keepVar censusPowerVar (by decide) d
      (by intro j hj;rw [hdc.two];exact (Nat.pow_le_pow_right (by decide) (by omega)).trans_lt hcenter)
      (by rw [hdk];omega) (by omega)).mono ?_ ?_
    · rw [hdk]
      omega
    · rintro e ⟨he,hes,hef⟩
      exact ⟨by simpa only [hdc.two,hdk] using he,hes,hef⟩
  refine Hs.seq (t2 := 1) hp2 fun e ⟨hep,hes,hef⟩ => ?_
  refine (hs_copy C keepVar censusPowerVar e (by decide)).mono le_rfl ?_
  rintro f rfl
  have hec : Cst e := Cst.of_fr hdc hef (by decide)
  refine ⟨?_,by simpa only [DS.set_env_self,centerCount] using hep,?_,?_,?_⟩
  · rw [DS.set_env_ne _ _ (by decide),hef _ (by decide),hdn]
    rfl
  · exact hes.trans (hds.trans hbs)
  · exact Cst.of_fr (T := [keepVar]) hec (Fr.set _ _ (by decide)) (by decide)
  · exact Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.weaken hdf (by decide))
        (Fr.trans (Fr.weaken hef (by decide)) (Fr.set _ _ (by decide))))

end NearQuarticWires.StageCertificateControl
