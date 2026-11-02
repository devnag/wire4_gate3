import Proof.Quartic.StageCertTests.SignedEntry
import Proof.Gates.CounterMachine.CellTablesConv

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms.SInt (encS encS_div encS_mod)
open NearCubicGates.Close.CounterMachine.CellTables (u4)
open StageRecovery (magnitudeVar signVar)

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the current conjunction bit is separate from native-reader scratch. -/
def flagVar : Fin VV := ⟨118,by decide⟩

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the exact nonnegative strict threshold is retained across one table scan. -/
def thresholdVar : Fin VV := ⟨119,by decide⟩

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
a negative signed moment always passes a nonnegative threshold;
otherwise its magnitude is compared strictly. -/
def testNativeFlag : St VV MM :=
  .seq (.op (.dm u4 v2 magnitudeVar signVar))
    (.ite (.eq signVar v1) skipS
      (.ite (.lt magnitudeVar thresholdVar) skipS (.op (.zero flagVar))))

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the native sign and magnitude comparison is the literal signed strict test. -/
theorem native_pass_iff (z : ℤ) (bound : ℕ) :
    (encS z % 2 = 1 ∨ encS z / 2 < bound) ↔ z < (bound : ℤ) := by
  rw [encS_mod,encS_div]
  by_cases hz : z < 0
  · simp [hz]
    exact lt_of_lt_of_le hz (Int.natCast_nonneg bound)
  · have ha : (z.natAbs : ℤ) = z := by
      rw [Int.natCast_natAbs,abs_of_nonneg (by omega)]
    simp only [hz,if_false,show (0:ℕ) ≠ 1 by decide,false_or]
    omega

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the actual binary program updates one conjunction bit with the
exact strict signed moment test, preserving all external streams. -/
theorem testNativeFlag_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (z : ℤ) (bound : ℕ) (flag : Bool)
    (hv : a.env u4 = encS z) (hb : a.env thresholdVar = bound)
    (hf : a.env flagVar = flag.toNat) (hfour : 4 ≤ 2 ^ C.Wd) :
    Hs C testNativeFlag a 8 (fun b =>
      b.env flagVar = (flag && decide (z < (bound : ℤ))).toNat ∧ b.sh = a.sh ∧
      Fr a b [magnitudeVar,signVar,flagVar,vJ]) := by
  unfold testNativeFlag
  refine (Hs.seq (t2 := 6) (hs_dm C u4 v2 magnitudeVar signVar a
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hc.two];norm_num) (by rw [hc.two];exact hfour))
    fun b he => ?_).mono (by omega) (fun _ h => h)
  subst b
  let s := (a.set magnitudeVar (a.env u4/a.env v2)).set signVar (a.env u4%a.env v2)
  have hsm : s.env magnitudeVar = encS z/2 := by
    simp (config := {decide := true}) [s,DS.set,hv,hc.two]
  have hss : s.env signVar = encS z%2 := by simp [s,hv,hc.two]
  have hsb : s.env thresholdVar = bound := by simp (config := {decide := true}) [s,DS.set,hb]
  have hsf : s.env flagVar = flag.toNat := by simp (config := {decide := true}) [s,DS.set,hf]
  have hsone : s.env v1 = 1 := by simp (config := {decide := true}) [s,DS.set,hc.one]
  have hp := native_pass_iff z bound
  change Hs C (.ite (.eq signVar v1) skipS
    (.ite (.lt magnitudeVar thresholdVar) skipS (.op (.zero flagVar)))) s 6 _
  refine Hs.ite (show signVar ≠ v1 by decide) (fun ht => ?_) (fun ht => ?_)
  · have hs1 : encS z%2 = 1 := by simpa only [Cnd.eval,hss,hsone,decide_eq_true_eq] using ht
    have hz : z < (bound:ℤ) := hp.mp (Or.inl hs1)
    refine (skip_spec (C := C) s).mono (by omega) ?_
    rintro b rfl
    exact ⟨by rw [DS.set_env_ne _ _ (by decide),hsf];simp [hz],rfl,
      Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩
  · have hs1 : encS z%2 ≠ 1 := by simpa only [Cnd.eval,hss,hsone,decide_eq_false_iff_not] using ht
    refine Hs.ite (show magnitudeVar ≠ thresholdVar by decide) (fun hm => ?_) (fun hm => ?_)
    · have hmag : encS z/2 < bound := by simpa only [Cnd.eval,hsm,hsb,decide_eq_true_eq] using hm
      have hz : z < (bound:ℤ) := hp.mp (Or.inr hmag)
      refine (skip_spec (C := C) s).mono (by omega) ?_
      rintro b rfl
      exact ⟨by rw [DS.set_env_ne _ _ (by decide),hsf];simp [hz],rfl,
        Fr.trans (Fr.set _ _ (by decide))
          (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩
    · have hmag : ¬encS z/2 < bound := by simpa only [Cnd.eval,hsm,hsb,decide_eq_false_iff_not] using hm
      have hz : ¬z < (bound:ℤ) := by intro h;rcases hp.mpr h with h|h;exact hs1 h;exact hmag h
      refine (hs_zero C flagVar s).mono (by omega) ?_
      rintro b rfl
      exact ⟨by simp [hz],rfl,
        Fr.trans (Fr.set _ _ (by decide))
          (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩

end NearQuarticWires.StageCertTests
