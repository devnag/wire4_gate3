import Proof.Quartic.StageOutput.Normalize
import Proof.Quartic.Cells.ParametersOutputCodec

/-!
# Printing the reduced nonnegative rational outputs

Paper: `sec:algorithm`, paper/paper.tex, and `prop:time`. The program reduces the natural numerator and positive
denominator and writes their exact canonical sign-magnitude encoding.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def rationalPrinter : St VV :=
  .seq normalizeProgram (.seq (emitL (natWord 0)) (printVars [reducedNum, reducedDen]))

def rationalScratch : List (Fin VV) := normalScratch ++ pvT

theorem rationalPrinter_spec {C : Ctx} (a : DS VV) (hc : Cst a) (hv : Valid C a)
    (hW : 3 ≤ C.Wd) (N D M : ℕ) (hN : a.env normalNum = N) (hD : a.env normalDen = D)
    (hd : 0 < D) (hNM : N ≤ M) (hDM : D ≤ M) (hcap : 2 * M ≤ 2 ^ C.Wd) :
    Hs C rationalPrinter a (14 * (Nat.size N + Nat.size D) + 80 * C.Wd + 300) (fun b =>
      b.out = a.out ++ ratWord ((N : ℚ) / D) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      Cst b ∧ Valid C b ∧ FrS a b rationalScratch) := by
  refine Hx.hs (Hs.then (Hs.addValid (by omega) hv
    (normalizeProgram_spec a hc N D M hN hD hd hNM hDM hcap))
    (fun b ⟨⟨bn, bd, bp, bw, bo, bc, bf⟩, bv⟩ n1 hn1 => ?_))
  refine Hs.then (Hs.addValid (by omega) bv (emitL_spec (C := C) (natWord 0) b))
    (fun d ⟨⟨dout, dp, dw, df⟩, dv⟩ n2 hn2 => ?_)
  have dc : Cst d := Cst.of_fr bc df (by decide) (by rw [df vPOS (by decide), dp]; exact bc.pos)
  have dn : d.env reducedNum = N / Nat.gcd N D := by rw [df reducedNum (by decide), bn]
  have dd : d.env reducedDen = D / Nat.gcd N D := by rw [df reducedDen (by decide), bd]
  refine Hs.last (printVars_spec (C := C) [reducedNum, reducedDen] (by decide) hW d dc dv) ?_
  rintro e ⟨eo, ep, ew, ec, ev, ef⟩ n3 hn3
  refine ⟨⟨?_, by rw [ep, dp, bp], by rw [ew, dw, bw], ec, ev, ?_⟩, ?_⟩
  · rw [eo, dout, bo, Cells.ratWord_nonnegative_quotient N D hd]
    simp [dn, dd, List.append_assoc]
  · exact FrS.trans (bf.weaken (fun y hy => List.mem_append_left _ hy))
      (FrS.trans (df.toS.weaken (by
        intro y hy
        simp only [List.mem_singleton] at hy
        subst hy
        decide)) (ef.weaken (fun y hy => List.mem_append_right _ hy)))
  · norm_num [natWord, natBitLength] at hn2
    simp only [List.length_cons, List.length_nil, pvCost] at hn3
    omega

end NearQuarticWires.StageOutput
