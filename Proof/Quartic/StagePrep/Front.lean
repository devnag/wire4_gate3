import Proof.Quartic.StagePrep.Initialize
import Proof.Quartic.StagePrep.CensusCall
import Proof.Quartic.StagePrep.Reparse

/-!
# The complete public admission computation

Paper: normalized calls, paper/paper.tex, and
parameter preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open Classical

/-- The public admission computation of `sec:counting`, paper/paper.tex includes the actual physical wire census. -/
def preparationFront (B1 B2 : ℕ) : St VV :=
  .seq initialConstants (.seq resetCensus (.seq censusCall (parseAdmission B1 B2)))

/-- The public preparation budget of `prop:time`,
paper/paper.tex, is independent of the witness. -/
def frontCost (B1 B2 L : ℕ) : ℕ :=
  3000 * (L + 2) ^ 3 + admCost B1 B2 + 100

/-- The computation of `sec:counting`, paper/paper.tex returns
the exact call parse and admission flag; no witness is read. -/
theorem preparationFront_spec (C : Ctx) (B1 B2 : ℕ) (c : Call)
    (hcw : C.cw = callWord c) (hW : 2 * C.cw.length + 8 ≤ C.Wd)
    (hL : 2 * C.cw.length + 4 < 2 ^ C.Wd)
    (hA : (B1 + B2 + 5) * ((callWord c).length + 1) ≤ C.Wd) :
    Hs C (preparationFront B1 B2) a0 (frontCost B1 B2 C.cw.length)
      (fun b => ParseOut c b ∧ b.env vADM = bnat (Transfer.Admitted4 B1 B2 c) ∧
        b.env censusTotal = Transfer.callWires c ∧
        b.env censusUnit = bnat (Transfer.UnitTop c.first ∧ Transfer.UnitTop c.second) ∧
        b.cp = (callWord c).length ∧ b.wq = 0 ∧ b.out = [] ∧ Cst b) := by
  unfold preparationFront
  refine Hx.hs (Hs.then (initialConstants_spec C (by omega))
    (fun b ⟨hbc, hbcp, hbwq, hbout, _⟩ n1 hn1 => ?_))
  refine Hs.then (resetCensus_spec C b hbc)
    (fun d ⟨hdt, hdf, hdcp, hdwq, hdout, hdc, _⟩ n2 hn2 => ?_)
  refine Hs.then (censusCall_spec C c d hdc (hdcp.trans hbcp) hdt hdf hcw hW hL)
    (fun e ⟨het, hef, _, hewq, heout, hec, _⟩ n3 hn3 => ?_)
  refine Hs.last (parseAdmission_spec C B1 B2 c e hec het hef hcw hW (by omega) hA)
    (fun f ⟨hfp, hfa, hft, hfu, hfcp, hfwq, hfout, hfc, _⟩ n4 hn4 => ?_)
  refine ⟨⟨hfp, hfa, hft, hfu, hfcp, ?_, ?_, hfc⟩, ?_⟩
  · exact hfwq.trans (hewq.trans (hdwq.trans hbwq))
  · exact hfout.trans (heout.trans (hdout.trans hbout))
  · unfold frontCost parseCost at *
    have hpos : 1 ≤ (C.cw.length + 2) ^ 3 := Nat.pow_pos (by omega)
    omega

/-- The public preparation budget in `prop:time`,
paper/paper.tex, has an explicit cubic bound. -/
theorem frontCost_le (B1 B2 L : ℕ) :
    frontCost B1 B2 L ≤ (24000 + admCost B1 B2 + 100) * (L + 1) ^ 3 := by
  have hx : L + 2 ≤ 2 * (L + 1) := by omega
  have hp := Nat.pow_le_pow_left hx 3
  have hpos : 1 ≤ (L + 1) ^ 3 := Nat.pow_pos (by omega)
  rw [mul_pow] at hp
  unfold frontCost
  nlinarith

/-- The public admission computation satisfies the polynomial
cost shape of `prop:time`, paper/paper.tex. -/
theorem frontCost_poly (B1 B2 : ℕ) :
    Program.PolyCost (fun c _ => frontCost B1 B2 (callWord c).length) :=
  ⟨24000 + admCost B1 B2 + 100, 3, fun c _ => frontCost_le B1 B2 (callWord c).length⟩

end NearQuarticWires.StagePrep
