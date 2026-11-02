import Proof.Quartic.StageModularCuts.KernelMagnitude
import Proof.Quartic.StageModularCuts.KernelCorrection

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms

def coefficientProgram : Program :=
  .seq magnitudeDivision (.seq correction (SInt.join remainder coefficient sign flag rewind))

def coefficientFinal (a : State) (p : ℕ) (z : ℤ) (q : ℕ) : State :=
  let a1 := divided (splitState a p z) (p + 1) z.natAbs q
  let a2 := corrected a1 (p + 1) q (z.natAbs % q) (decide (z < 0))
  (a2.sets coefficient (frame (binary (p + 1) (SInt.encS (z % (q : ℤ)))))).setv sign 0

def coefficientCost (p : ℕ) : ℕ :=
  2 * BinW.divCost (p + 1) + 288 * p + 387

/-- `lem:print`, paper/paper.tex: one signed weak-cut
coefficient is replaced by its canonical residue using only binary
fixed-width splitting, division, subtraction, and serialization. -/
theorem coefficientProgram_spec (cap p : ℕ) (a : State) (z : ℤ) (q x u v t : ℕ)
    (hz : SInt.SNumOn a coefficient p z) (hw : Words a (p + 1) x q u v t)
    (hc : Clear a) (hs : a.val sign = 0) (hq : 0 < q) (hqfit : q ≤ 2 ^ p)
    (hcap : 2 * (p + 1) + 1 ≤ cap) :
    WXExec cap coefficientProgram a (coefficientFinal a p z q) (coefficientCost p) := by
  let a1 := divided (splitState a p z) (p + 1) z.natAbs q
  have h1 := magnitudeDivision_spec cap p a z q x u v t hz hw hc hs hq hqfit hcap
  have hw1 := divided_words (splitState a p z) (p + 1) z.natAbs q u v t
    (splitState_words a p q x u v t z hw)
  have hc1 := divided_clear (splitState a p z) (p + 1) z.natAbs q (splitState_clear a p z hc)
  have hs1 : a1.val sign = (decide (z < 0)).toNat := by simp [a1, divided, splitState]
  have h2 := correction_spec cap (p + 1) a1 z.natAbs q (z.natAbs / q) (z.natAbs % q)
    (decide (z < 0)) hw1 hc1 hs1 hq (by rw [pow_succ]; omega) (Nat.mod_lt _ hq) hcap
  let a2 := corrected a1 (p + 1) q (z.natAbs % q) (decide (z < 0))
  have hw2 := corrected_words a1 (p + 1) z.natAbs q (z.natAbs / q) (z.natAbs % q)
    (decide (z < 0)) hw1
  obtain ⟨hc2, hs2⟩ := corrected_clear a1 (p + 1) q (z.natAbs % q) (decide (z < 0)) hc1 hs1
  have hco1 : NumOn a1 coefficient (p + 1) (SInt.encS z) :=
    BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne
      (BinW.numOn_setv (BinW.numOn_sets_ne hz.1 (by decide) _) _ _) (by decide) _)
      (by decide) _) (by decide) _
  have hco2 := corrected_coefficient a1 (p + 1) q (z.natAbs % q) (SInt.encS z) (decide (z < 0)) hco1
  let r := StageRecovery.signedNaturalResidue q z.natAbs (decide (z < 0))
  have hr : r < 2 ^ p := lt_of_lt_of_le (signed_residue_lt q z.natAbs (decide (z < 0)) hq) hqfit
  have hrem : NumOn a2 remainder (p + 1) r := hw2.remainder
  have h3 := SInt.join_spec cap p (by decide) (by decide) (by decide) (by decide)
    a2 r (SInt.encS z) false hrem hr hco2 hs2 hc2.flag hc2.rewind hcap
  have he : SInt.sval r false = z % (q : ℤ) :=
    StageRecovery.signedNaturalResidue_eq q hq z
  rw [he] at h3
  exact WXExec.seq' cap h1 (WXExec.seq h2 h3) (by unfold coefficientCost; omega)

/-- `lem:print` and `prop:time`, paper/paper.tex: reducing one coefficient has quadratic bit-width cost. -/
theorem coefficientCost_le (p : ℕ) : coefficientCost p ≤ 2000 * (p + 2) ^ 2 := by
  unfold coefficientCost BinW.divCost
  nlinarith

end NearQuarticWires.StageModularCuts
