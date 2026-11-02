import Proof.Quartic.StageMain.PackedPoint

/-!
# Signed accumulation for a sampled threshold input

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. Each selected coordinate contributes its
weight to separate positive and negative binary accumulators. Unselected
coordinates contribute zero, and the comparison retains inclusive ties.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicGates.Close.Dispatch

def scoreUpdate : St VV := .ite (.eq pointBit v1)
  (.ite (.eq t8 vZ) (.op (.add scorePositive t3)) (.op (.add scoreNegative t3))) skipS

def scoreUpdateScratch : List (Fin VV) := [vJ, scorePositive, scoreNegative]

theorem scoreUpdate_spec {C : Ctx} (a : DS VV) (hc : Cst a) (w : ℤ) (bit : Bool)
    (hbit : a.env pointBit = bit.toNat) (hsg : a.env t8 = if w < 0 then 1 else 0)
    (hmag : a.env t3 = w.natAbs)
    (hcap : a.env scorePositive + a.env scoreNegative + w.natAbs < 2 ^ C.Wd) :
    Hs C scoreUpdate a 3 (fun b =>
      b.env scorePositive = a.env scorePositive + (if bit then w.toNat else 0) ∧
      b.env scoreNegative = a.env scoreNegative + (if bit then (-w).toNat else 0) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b scoreUpdateScratch) := by
  cases bit with
  | false =>
    have he : (Cnd.eq pointBit v1).eval a = false := by simp [Cnd.eval, hbit, hc.one]
    refine Hs.mono (Hs.iteF (show pointBit ≠ v1 by decide) he (skip_spec a)) (by omega) ?_
    rintro b rfl
    refine ⟨by simp (config := { decide := true }), by simp (config := { decide := true }),
      rfl, rfl, rfl, hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩
  | true =>
    have he : (Cnd.eq pointBit v1).eval a = true := by simp [Cnd.eval, hbit, hc.one]
    refine Hs.iteT (c := .eq pointBit v1) (show pointBit ≠ v1 by decide) he ?_
    cases w with
    | ofNat n =>
      have hs : (Cnd.eq t8 vZ).eval a = true := by simp [Cnd.eval, hsg, hc.z]
      refine Hs.mono (Hs.iteT (show t8 ≠ vZ by decide) hs
        (hs_add C scorePositive t3 a (by decide) (by rw [hmag]; omega))) le_rfl ?_
      rintro b rfl
      refine ⟨?_, ?_, rfl, rfl, rfl, hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩
      · simp [hmag]
      · simp (config := { decide := true })
    | negSucc n =>
      have hs : (Cnd.eq t8 vZ).eval a = false := by simp [Cnd.eval, hsg, hc.z]
      refine Hs.mono (Hs.iteF (show t8 ≠ vZ by decide) hs
        (hs_add C scoreNegative t3 a (by decide) (by rw [hmag]; omega))) le_rfl ?_
      rintro b rfl
      refine ⟨?_, ?_, rfl, rfl, rfl, hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩
      · simp (config := { decide := true })
      · simp [hmag]

end NearQuarticWires.StageMain
