import Proof.Quartic.StageModularCuts.KernelSign

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms

def correction : Program := .ifr sign negativeCorrection WMX.skip

def corrected (a : State) (W q v : ℕ) (s : Bool) : State :=
  if s then negativeState a W q v else a

/-- `lem:print`, paper/paper.tex: the sign branch
executes binary modular correction only for negative coefficients. -/
theorem correction_spec (cap W : ℕ) (a : State) (x q u v : ℕ) (s : Bool)
    (hw : Words a W x q u v 0) (hc : Clear a) (hs : a.val sign = s.toNat)
    (hq : 0 < q) (hfit : 2 * q ≤ 2 ^ W) (hv : v < q)
    (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap correction a (corrected a W q v s)
      (82 * W + 17 + BinW.divCost W) := by
  cases s with
  | false =>
    exact (WXExec.ifrF hs (WXExec.skip cap a)).mono (by omega)
  | true =>
    exact (WXExec.ifrT (by simp [hs])
      (negativeCorrection_spec cap W a x q u v 0 hw hc hs hq hfit hv hcap)).mono (by omega)

/-- `lem:print`, paper/paper.tex: the corrected work
word is the canonical residue, with the arithmetic workspace retained. -/
theorem corrected_words (a : State) (W x q u v : ℕ) (s : Bool)
    (hw : Words a W x q u v 0) :
    Words (corrected a W q v s) W (if s then q - v else x) q
      (if s then (q - v) / q else u) (if s then (q - v) % q else v) 0 := by
  cases s with
  | false => exact hw
  | true => exact negativeState_words a W x q u v 0 hw

/-- `lem:print`, paper/paper.tex: sign correction
restores the sign and leaves all arithmetic counters zero. -/
theorem corrected_clear (a : State) (W q v : ℕ) (s : Bool)
    (hc : Clear a) (hs : a.val sign = s.toNat) :
    Clear (corrected a W q v s) ∧ (corrected a W q v s).val sign = 0 := by
  cases s with
  | false => exact ⟨hc, hs⟩
  | true => exact ⟨negativeState_clear a W q v hc, by simp [corrected, negativeState, divided]⟩

/-- `lem:print`, paper/paper.tex: division and sign
correction leave the original signed field available for its writer. -/
theorem corrected_coefficient (a : State) (W q v e : ℕ) (s : Bool)
    (ha : NumOn a coefficient W e) :
    NumOn (corrected a W q v s) coefficient W e := by
  cases s with
  | false => exact ha
  | true =>
    exact BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne
      (BinW.numOn_sets_ne (BinW.numOn_setv ha _ _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _

end NearQuarticWires.StageModularCuts
