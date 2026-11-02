import Proof.Quartic.StagePrep.Front

/-!
# Physical execution of the public admission computation

Paper: normalized calls, paper/paper.tex, and
`prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Interfaces
open Classical

/-- The preparation computation of `prop:time`, paper/paper.tex, is a physical word-program execution with the
exact parsed call, actual wire count and admission flag. -/
theorem preparationFront_physical (C : Ctx) (B1 B2 : ℕ) (c : Call)
    (inp : List Bool) (p0 cap : ℕ)
    (hcw : C.cw = callWord c) (hW : 2 * C.cw.length + 8 ≤ C.Wd)
    (hL : 2 * C.cw.length + 4 < 2 ^ C.Wd)
    (hA : (B1 + B2 + 5) * ((callWord c).length + 1) ≤ C.Wd)
    (hlay : WitLayout inp p0 C.wit)
    (hcapW : 2 * C.Wd + 1 ≤ cap) (hcapC : C.cw.length + 1 ≤ cap)
    (hcapI : p0 + 4 * C.wit.length + 4 ≤ cap)
    (hbudget : frontCost B1 B2 C.cw.length ≤ cap) :
    ∃ b, WXExec cap (comp (preparationFront B1 B2))
        (E C inp p0 a0) (E C inp p0 b)
        (frontCost B1 B2 C.cw.length * KC C.Wd) ∧
      ParseOut c b ∧ b.env vADM = bnat (Transfer.Admitted4 B1 B2 c) ∧
      b.env censusTotal = Transfer.callWires c ∧
      b.cp = (callWord c).length ∧ b.wq = 0 ∧ b.out = [] := by
  obtain ⟨b, n, hex, hn, hparse, hadm, htotal, _, hcp, hwq, hout, _⟩ :=
    preparationFront_spec C B1 B2 c hcw hW hL hA
  have ha : Valid C (a0 (V := VV)) := by
    refine ⟨?_, by simp [a0], by simp [a0]⟩
    intro x
    exact Nat.pow_pos (by decide)
  have hrun := (comp_ok C inp p0 cap hlay (by omega) (by omega)
    hcapW hcapC hcapI hex ha (by simpa only [a0, List.length_nil,
      Nat.zero_add] using hn.trans hbudget)).1
  exact ⟨b, WXExec.mono hrun (Nat.mul_le_mul_right _ hn),
    hparse, hadm, htotal, hcp, hwq, hout⟩

end NearQuarticWires.StagePrep
