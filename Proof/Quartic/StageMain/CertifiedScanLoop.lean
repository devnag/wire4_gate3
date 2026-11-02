import Proof.Quartic.StageMain.CertifiedScanStep

/-!
# Linear traversal of certified-column flags

Step 4 of `sec:algorithm`, paper/paper.tex: all
certificate flags are scanned once to reach the chosen seed. Each
flag contributes its Boolean value to the certified-column count.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift

def trueCount (bits : List Bool) : ℕ := (bits.map Bool.toNat).sum

theorem trueCount_le_length (bits : List Bool) : trueCount bits ≤ bits.length := by
  induction bits with
  | nil => simp [trueCount]
  | cons b bs ih =>
      simp only [trueCount, List.map_cons, List.sum_cons, List.length_cons] at *
      cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

theorem certificateLoop_run (C : Ctx) (bits rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hflag : a.env t0 = (frameFlag bits).toNat)
    (hin : C.inp.drop a.ip = framePayload bits ++ rest)
    (hcount : a.env certifiedCount + trueCount bits < 2 ^ C.Wd)
    (hindex : a.env columnCounter + bits.length < 2 ^ C.Wd) :
    Hs C (.loop (.eq t0 v1) countCertificateBody) a (9 * bits.length + 2) (fun b =>
      b.env t0 = 0 ∧ b.ip = a.ip + 2 * bits.length ∧
      b.env certifiedCount = a.env certifiedCount + trueCount bits ∧
      b.env columnCounter = a.env columnCounter + bits.length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b certificateScratch) := by
  induction bits generalizing a with
  | nil =>
      have he : (Cnd.eq t0 v1).eval a = false := by
        simp [Cnd.eval, hflag, frameFlag, hc.one]
      refine ⟨a, 2, Ex.loopF (show t0 ≠ v1 by decide) he, by simp, ?_⟩
      exact ⟨by simpa [frameFlag] using hflag, by simp, by simp [trueCount],
        by simp, rfl, hc, Fr.refl _ _⟩
  | cons bit bits ih =>
      have he : (Cnd.eq t0 v1).eval a = true := by
        simp [Cnd.eval, hflag, frameFlag, hc.one]
      have hinput : C.inp.drop a.ip = bit :: frameFlag bits :: (framePayload bits ++ rest) := by
        change C.inp.drop a.ip = (bit :: frame bits) ++ rest at hin
        rw [frame_decompose bits] at hin
        simpa only [List.cons_append] using hin
      have hsum : trueCount (bit :: bits) = bit.toNat + trueCount bits := by
        simp [trueCount]
      obtain ⟨b, n, hb, hn, hbeq⟩ := countCertificateBody_run C a bit (frameFlag bits)
        (framePayload bits ++ rest) hinput (by rw [hsum] at hcount; omega)
          (by simp only [List.length_cons] at hindex; omega)
      subst b
      have hbf := certificateStep_fr a bit (frameFlag bits)
      have hbc := Cst.of_fr hc hbf (by decide)
      have hbin : C.inp.drop (certificateStep a bit (frameFlag bits)).ip =
          framePayload bits ++ rest := by
        change C.inp.drop (a.ip + 2) = _
        rw [← List.drop_drop, hinput]
        rfl
      have hbcnt : (certificateStep a bit (frameFlag bits)).env certifiedCount =
          a.env certifiedCount + bit.toNat := by
        simp (config := {decide := true}) [certificateStep, DS.set]
      have hbidx : (certificateStep a bit (frameFlag bits)).env columnCounter =
          a.env columnCounter + 1 := by
        simp (config := {decide := true}) [certificateStep, DS.set]
      obtain ⟨d, k, hd, hk, hdz, hdi, hdcount, hdindex, hdrest, hdc, hdf⟩ :=
        ih (certificateStep a bit (frameFlag bits)) hbc (by simp [certificateStep]) hbin
          (by rw [hbcnt]; rw [hsum] at hcount; omega)
          (by rw [hbidx]; simp only [List.length_cons] at hindex; omega)
      refine ⟨d, n + k + 2, Ex.loopT (show t0 ≠ v1 by decide) he hb hd, by simp; omega, ?_⟩
      refine ⟨hdz, ?_, ?_, ?_, hdrest, hdc, hbf.trans hdf⟩
      · rw [hdi]
        change a.ip + 2 + 2 * bits.length = a.ip + 2 * (bit :: bits).length
        simp only [List.length_cons]
        omega
      · rw [hdcount, hbcnt, hsum]
        omega
      · rw [hdindex, hbidx]
        simp only [List.length_cons]
        omega

end NearQuarticWires.StageMain.Controller
