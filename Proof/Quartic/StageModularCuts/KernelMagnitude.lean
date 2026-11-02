import Proof.Quartic.StageModularCuts.KernelData

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms

def splitState (a : State) (p : ℕ) (z : ℤ) : State :=
  (a.sets magnitude (frame (binary (p + 1) z.natAbs))).setv sign (decide (z < 0)).toNat

def magnitudeDivision : Program :=
  .seq (SInt.split coefficient magnitude sign flag rewind) divide

/-- `lem:print`, paper/paper.tex: decoding the signed
field keeps every unrelated tape and all four arithmetic counters. -/
theorem splitState_words (a : State) (p q x u v t : ℕ) (z : ℤ)
    (hw : Words a (p + 1) x q u v t) :
    Words (splitState a p z) (p + 1) z.natAbs q u v t := by
  constructor
  · exact BinW.numOn_setv (BinW.numOn_sets_self a magnitude _ _ hw.input.2) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne hw.divisor (by decide) _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne hw.quotient (by decide) _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne hw.remainder (by decide) _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne hw.temporary (by decide) _) _ _

/-- `lem:print`, paper/paper.tex: signed decoding uses
only its sign register in addition to the magnitude tape. -/
theorem splitState_clear (a : State) (p : ℕ) (z : ℤ) (hc : Clear a) :
    Clear (splitState a p z) := by
  constructor
  · simpa [splitState, flag, sign] using hc.flag
  · simpa [splitState, rewind, sign] using hc.rewind
  · simpa [splitState, rounds, sign] using hc.rounds
  · simpa [splitState, counter, sign] using hc.counter

/-- `lem:print`, paper/paper.tex: the actual signed
binary field is split and its magnitude divided by the binary modulus.
The extra work bit permits the boundary modulus equal to `2^p`. -/
theorem magnitudeDivision_spec (cap p : ℕ) (a : State) (z : ℤ) (q x u v t : ℕ)
    (hz : SInt.SNumOn a coefficient p z) (hw : Words a (p + 1) x q u v t)
    (hc : Clear a) (hs : a.val sign = 0) (hq : 0 < q) (hqfit : q ≤ 2 ^ p)
    (hcap : 2 * (p + 1) + 1 ≤ cap) :
    WXExec cap magnitudeDivision a (divided (splitState a p z) (p + 1) z.natAbs q)
      (76 * p + 126 + BinW.divCost (p + 1)) := by
  have h1 := SInt.split_spec cap p (by decide) (by decide) a z x
    hz hw.input hs hc.flag hc.rewind hcap
  have h2 := divide_spec cap (p + 1) (splitState a p z) z.natAbs q u v t
    (splitState_words a p q x u v t z hw) (splitState_clear a p z hc)
    (by have hh := hz.2; rw [pow_succ]; omega)
    hq (by rw [pow_succ]; omega) hcap
  exact WXExec.seq' cap h1 h2 (by omega)

end NearQuarticWires.StageModularCuts
