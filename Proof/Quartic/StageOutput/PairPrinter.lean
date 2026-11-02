import Proof.Quartic.StageOutput.Center

/-!
# Printing the center and radius in order

Paper: `sec:algorithm`, paper/paper.tex, and `prop:time`. The center is reduced and printed first; the saved radius
and common positive denominator are retained through that computation and
then printed by the same rational codec.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def pairPrinter : St VV := .seq rationalPrinter
  (.seq (.op (.copy normalNum savedRadius)) rationalPrinter)

def pairPrintCost (N R D W : ℕ) : ℕ := 28 * (Nat.size N + Nat.size R + Nat.size D) + 160 * W + 605

theorem pairPrinter_spec {C : Ctx} (a : DS VV) (hc : Cst a) (hv : Valid C a)
    (hW : 3 ≤ C.Wd) (N R D M : ℕ)
    (hN : a.env normalNum = N) (hR : a.env savedRadius = R) (hD : a.env normalDen = D)
    (hd : 0 < D) (hNM : N ≤ M) (hRM : R ≤ M) (hDM : D ≤ M) (hcap : 2 * M ≤ 2 ^ C.Wd) :
    Hs C pairPrinter a (pairPrintCost N R D C.Wd) (fun b =>
      b.out = a.out ++ outputWord ((N : ℚ) / D, (R : ℚ) / D) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ Cst b ∧ Valid C b) := by
  refine Hx.hs (Hs.then (rationalPrinter_spec a hc hv hW N D M hN hD hd hNM hDM hcap)
    (fun b ⟨bo, bp, bw, bc, bv, bf⟩ n1 hn1 => ?_))
  have br : b.env savedRadius = R := (bf _ (by decide) (by decide)).trans hR
  have bd : b.env normalDen = D := (bf _ (by decide) (by decide)).trans hD
  refine Hs.then (Hs.addValid (by omega) bv (hs_copy C normalNum savedRadius b (by decide)))
    (fun c ⟨hc', cv⟩ n2 hn2 => ?_)
  subst hc'
  refine Hs.last (rationalPrinter_spec _ (bc.set _ _ (by decide)) cv hW R D M
    (by simpa using br) (by simpa (config := { decide := true }) using bd) hd hRM hDM hcap) ?_
  rintro e ⟨eo, ep, ew, ec, ev, _⟩ n3 hn3
  refine ⟨⟨?_, by rw [ep, DS.set_cp, bp], by rw [ew, DS.set_wq, bw], ec, ev⟩, ?_⟩
  · rw [eo, DS.set_out, bo]
    simp only [outputWord, List.append_assoc]
  · unfold pairPrintCost
    omega

end NearQuarticWires.StageOutput
