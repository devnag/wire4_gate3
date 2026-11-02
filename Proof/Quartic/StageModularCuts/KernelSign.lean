import Proof.Quartic.StageModularCuts.KernelData

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: sign correction
computes `(q-r) mod q` using binary subtraction and division. -/
def negativeCorrection : Program :=
  .seq (WMX.dec sign) (.seq (BinW.copy magnitude modulus flag rewind)
    (.seq (BinW.sub magnitude remainder flag rewind) divide))

def negativeState (a : State) (W q v : ℕ) : State :=
  divided ((a.setv sign 0).sets magnitude (frame (binary W (q - v)))) W (q - v) q

/-- `lem:print`, paper/paper.tex: changing the sign
register leaves every binary work word intact. -/
theorem words_setSign (a : State) (W x q u v t s : ℕ)
    (hw : Words a W x q u v t) : Words (a.setv sign s) W x q u v t :=
  ⟨BinW.numOn_setv hw.input _ _, BinW.numOn_setv hw.divisor _ _,
   BinW.numOn_setv hw.quotient _ _, BinW.numOn_setv hw.remainder _ _,
   BinW.numOn_setv hw.temporary _ _⟩

/-- `lem:print`, paper/paper.tex: the sign register is
disjoint from all binary arithmetic counters. -/
theorem clear_setSign (a : State) (s : ℕ) (hc : Clear a) : Clear (a.setv sign s) := by
  constructor
  · simpa [flag, sign] using hc.flag
  · simpa [rewind, sign] using hc.rewind
  · simpa [rounds, sign] using hc.rounds
  · simpa [counter, sign] using hc.counter

/-- `lem:print`, paper/paper.tex: replacing the input
magnitude keeps the other four fixed-width words. -/
theorem words_setMagnitude (a : State) (W x q u v t y : ℕ)
    (hw : Words a W x q u v t) :
    Words (a.sets magnitude (frame (binary W y))) W y q u v t :=
  ⟨BinW.numOn_sets_self _ _ _ _ hw.input.2,
   BinW.numOn_sets_ne hw.divisor (by decide) _,
   BinW.numOn_sets_ne hw.quotient (by decide) _,
   BinW.numOn_sets_ne hw.remainder (by decide) _,
   BinW.numOn_sets_ne hw.temporary (by decide) _⟩

/-- `lem:print`, paper/paper.tex: word replacement
preserves all arithmetic counters. -/
theorem clear_setMagnitude (a : State) (W y : ℕ) (hc : Clear a) :
    Clear (a.sets magnitude (frame (binary W y))) :=
  ⟨hc.flag, hc.rewind, hc.rounds, hc.counter⟩

/-- `lem:print`, paper/paper.tex: a negative signed
coefficient is corrected by actual fixed-width arithmetic, including
zero residues and a modulus equal to the magnitude range. -/
theorem negativeCorrection_spec (cap W : ℕ) (a : State) (x q u v t : ℕ)
    (hw : Words a W x q u v t) (hc : Clear a) (hs : a.val sign = 1)
    (hq : 0 < q) (hfit : 2 * q ≤ 2 ^ W) (hv : v < q)
    (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap negativeCorrection a (negativeState a W q v)
      (82 * W + 16 + BinW.divCost W) := by
  have h1 := WXExec.dec cap sign a (by omega)
  have he : a.setv sign (a.val sign - 1) = a.setv sign 0 := by rw [hs]
  rw [he] at h1
  let a0 := a.setv sign 0
  have hw0 := words_setSign a W x q u v t 0 hw
  have hc0 := clear_setSign a 0 hc
  have h2 := BinW.copy_spec cap W (by decide) (by decide) a0 x q
    hw0.input hw0.divisor hc0.flag hc0.rewind hcap
  let a1 := a0.sets magnitude (frame (binary W q))
  have hw1 := words_setMagnitude a0 W x q u v t q hw0
  have hc1 := clear_setMagnitude a0 W q hc0
  have h3 := BinW.sub_spec cap W (by decide) (by decide) a1 q v
    hw1.input hw1.remainder hc1.flag hc1.rewind hv.le (by omega) hcap
  let a2 := a1.sets magnitude (frame (binary W (q - v)))
  have hw2 := words_setMagnitude a1 W q q u v t (q - v) hw1
  have hc2 := clear_setMagnitude a1 W (q - v) hc1
  have h4 := divide_spec cap W a2 (q - v) q u v t hw2 hc2
    (by omega) hq hfit hcap
  refine (WXExec.seq' cap h1 (WXExec.seq h2 (WXExec.seq h3 h4)) (by omega)).cast cap ?_ le_rfl
  simp only [a2, a1, a0, BinW.sets_sets, negativeState]

/-- `lem:print`, paper/paper.tex: sign correction
returns the canonical nonnegative residue and a cleared sign flag. -/
theorem negativeState_words (a : State) (W x q u v t : ℕ)
    (hw : Words a W x q u v t) :
    Words (negativeState a W q v) W (q - v) q ((q - v) / q) ((q - v) % q) 0 :=
  divided_words _ W (q - v) q u v t
    (words_setMagnitude _ W x q u v t (q - v) (words_setSign a W x q u v t 0 hw))

/-- `lem:print`, paper/paper.tex: sign correction
restores every arithmetic counter before the next coefficient. -/
theorem negativeState_clear (a : State) (W q v : ℕ) (hc : Clear a) :
    Clear (negativeState a W q v) :=
  divided_clear _ W (q - v) q (clear_setMagnitude _ W (q - v) (clear_setSign a 0 hc))

end NearQuarticWires.StageModularCuts
