import Proof.Quartic.StageMain.SeedReadStep
import Proof.Quartic.Algorithm.Algorithm

/-!
# Exact low-bit-first seed accumulation

`imp:seed`, paper/paper.tex, and Step 4 of
`sec:algorithm`: each seed payload bit is added with
its binary positional weight. The following source suffix is preserved.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.SampleCells

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift
open Algorithm.CellCall (prefixValue)

theorem prefixValue_cons_nat (bit : Bool) (bits : List Bool) :
    prefixValue (bit :: bits) = bit.toNat + 2 * prefixValue bits := by
  cases bit <;> rfl

theorem seedReadLoop_run (C : Ctx) (bits rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hflag : a.env t0 = (frameFlag bits).toNat)
    (hin : C.inp.drop a.ip = framePayload bits ++ rest)
    (hvalue : a.env seed + a.env seedPower * prefixValue bits < 2 ^ C.Wd)
    (hpower : a.env seedPower * 2 ^ bits.length < 2 ^ C.Wd) :
    Hs C (.loop (.eq t0 v1) seedReadBody) a (11 * bits.length + 2) (fun b =>
      b.env t0 = 0 ∧ b.ip = a.ip + 2 * bits.length ∧
      b.env seed = a.env seed + a.env seedPower * prefixValue bits ∧
      b.env seedPower = a.env seedPower * 2 ^ bits.length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b seedReadScratch) := by
  induction bits generalizing a with
  | nil =>
      have he : (Cnd.eq t0 v1).eval a = false := by
        simp [Cnd.eval, hflag, frameFlag, hc.one]
      refine ⟨a, 2, Ex.loopF (show t0 ≠ v1 by decide) he, by simp, ?_⟩
      exact ⟨by simpa [frameFlag] using hflag, by simp, by simp [prefixValue],
        by simp, rfl, hc, Fr.refl _ _⟩
  | cons bit bits ih =>
      have he : (Cnd.eq t0 v1).eval a = true := by
        simp [Cnd.eval, hflag, frameFlag, hc.one]
      have hinput : C.inp.drop a.ip = bit :: frameFlag bits :: (framePayload bits ++ rest) := by
        change C.inp.drop a.ip = (bit :: frame bits) ++ rest at hin
        rw [frame_decompose bits] at hin
        simpa only [List.cons_append] using hin
      have hvalue' : a.env seed + bit.toNat * a.env seedPower < 2 ^ C.Wd := by
        rw [prefixValue_cons_nat] at hvalue
        nlinarith
      have hpower' : 2 * a.env seedPower < 2 ^ C.Wd := by
        have hp : 1 ≤ 2 ^ bits.length := Nat.one_le_two_pow
        simp only [List.length_cons, pow_succ] at hpower
        nlinarith
      obtain ⟨b, n, hb, hn, hbeq⟩ := seedReadBody_run C a bit (frameFlag bits)
        (framePayload bits ++ rest) hinput hvalue' hpower'
      subst b
      have hbf := seedReadStep_fr a bit (frameFlag bits)
      have hbc := Cst.of_fr hc hbf (by decide)
      have hbin : C.inp.drop (seedReadStep a bit (frameFlag bits)).ip =
          framePayload bits ++ rest := by
        change C.inp.drop (a.ip + 2) = _
        rw [← List.drop_drop, hinput]
        rfl
      have hbvalue : (seedReadStep a bit (frameFlag bits)).env seed =
          a.env seed + bit.toNat * a.env seedPower := by
        simp (config := {decide := true}) [seedReadStep, DS.set]
      have hbpower : (seedReadStep a bit (frameFlag bits)).env seedPower =
          2 * a.env seedPower := by
        simp (config := {decide := true}) [seedReadStep, DS.set]
      obtain ⟨d, k, hd, hk, hdz, hdi, hdvalue, hdpower, hdrest, hdc, hdf⟩ :=
        ih (seedReadStep a bit (frameFlag bits)) hbc (by simp [seedReadStep]) hbin
          (by rw [hbvalue, hbpower]; rw [prefixValue_cons_nat] at hvalue; nlinarith)
          (by rw [hbpower]; simp only [List.length_cons, pow_succ] at hpower; nlinarith)
      refine ⟨d, n + k + 2, Ex.loopT (show t0 ≠ v1 by decide) he hb hd, by simp; omega, ?_⟩
      refine ⟨hdz, ?_, ?_, ?_, hdrest, hdc, hbf.trans hdf⟩
      · rw [hdi]
        change a.ip + 2 + 2 * bits.length = a.ip + 2 * (bit :: bits).length
        simp only [List.length_cons]
        omega
      · rw [hdvalue, hbvalue, hbpower, prefixValue_cons_nat]
        ring
      · rw [hdpower, hbpower]
        simp only [List.length_cons, pow_succ]
        ring

end NearQuarticWires.StageMain.SampleCells
