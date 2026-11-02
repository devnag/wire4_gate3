import Proof.Quartic.StageOutput.Powers
import Proof.Quartic.StageOutput.PairPrinter

/-!
# The complete arithmetic and printing sequence of Step 5

Paper: `sec:algorithm`, paper/paper.tex, and `prop:time`. Binary powers, signed endpoint rounding, center and radius
formation, and the two canonical rational encodings are executed in order.
The arithmetic workspace is explicitly bounded by its binary width.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def arithmeticCore : St VV := .seq powersProgram
  (.seq endpointPair (.seq centerProgram pairPrinter))

theorem pairPrintCost_le (N R D M W : ℕ) (hN : N ≤ M) (hR : R ≤ M) (hD : D ≤ M)
    (hcap : 2 * M ≤ 2 ^ W) : pairPrintCost N R D W ≤ 244 * W + 605 := by
  have hp : 0 < 2 ^ W := by positivity
  have hM : M < 2 ^ W := by omega
  have hn := Nat.size_le.mpr (hN.trans_lt hM)
  have hr := Nat.size_le.mpr (hR.trans_lt hM)
  have hd := Nat.size_le.mpr (hD.trans_lt hM)
  unfold pairPrintCost
  omega

theorem arithmeticCore_spec {C : Ctx} (d : Input) (B M : ℕ) (a : DS VV)
    (hc : Cst a) (hv : Valid C a) (hs : d.Stored a.env)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hnB : d.n ≤ B) (hkB : d.k ≤ B)
    (hw : 64 * (B + 1) ≤ C.Wd) (hD : 0 < d.denominator)
    (hG : 0 ≤ d.ceilValue) (hcenter : 0 ≤ d.floorValue + d.ceilValue)
    (hradius : 0 ≤ d.ceilValue - d.floorValue)
    (hadd : d.floorValue.natAbs + d.ceilValue.natAbs + 2 ^ (d.n + 1) + 2 < 2 ^ C.Wd)
    (hNM : d.centerNumerator ≤ M) (hRM : d.radiusNumerator ≤ M)
    (hDM : 2 ^ (d.n + 1) ≤ M) (hcap : 2 * M ≤ 2 ^ C.Wd) :
    Hs C arithmeticCore a (1000 * C.Wd + 1000) (fun b =>
      b.out = a.out ++ outputWord
        ((d.centerNumerator : ℚ) / (2 ^ (d.n + 1) : ℕ),
         (d.radiusNumerator : ℚ) / (2 ^ (d.n + 1) : ℕ)) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ Cst b ∧ Valid C b) := by
  refine Hx.hs (Hs.then (Hs.addValid (by omega) hv
    (powersProgram_spec a hc d.n d.k hs.1 hs.2.1 (by omega) (by omega)))
    (fun b ⟨⟨bn, bk, bp, bw, bo, bc, bf⟩, bv⟩ n1 hn1 => ?_))
  have bs : d.Stored b.env := d.stored_of_frame hs bf.toS (by decide)
  refine Hs.then (Hs.addValid (by omega) bv
    (endpointPair_spec d B b bc bs bn bk hf hnB hkB hw hD hG))
    (fun e ⟨⟨ef, eg, _, ep, ew, eo, ec, efr⟩, ev⟩ n2 hn2 => ?_)
  have en : e.env powerN = 2 ^ d.n := (efr _ (by decide) (by decide)).trans bn
  have efmag : e.env savedF = d.floorValue.natAbs := by
    split_ifs at ef <;> simpa only [Int.natAbs_natCast, Int.natAbs_neg] using congrArg Int.natAbs ef
  have egmag : e.env savedG = d.ceilValue.natAbs := by
    simpa only [Int.natAbs_natCast] using congrArg Int.natAbs eg
  have eadd : e.env savedF + e.env savedG + 2 * e.env powerN + 2 < 2 ^ C.Wd := by
    rw [efmag, egmag, en]
    simpa only [pow_succ, Nat.mul_comm] using hadd
  refine Hs.then (Hs.addValid (by omega) ev
    (centerProgram_spec d e ec ef eg en hcenter hradius eadd))
    (fun f ⟨⟨fn, fr, fd, fp, fw, fo, fc, _⟩, fv⟩ n3 hn3 => ?_)
  refine Hs.last (pairPrinter_spec f fc fv (by omega)
    d.centerNumerator d.radiusNumerator (2 ^ (d.n + 1)) M fn fr fd (by positivity) hNM hRM hDM hcap) ?_
  rintro g ⟨go, gp, gw, gc, gv⟩ n4 hn4
  refine ⟨⟨by rw [go, fo, eo, bo], by rw [gp, fp, ep, bp],
    by rw [gw, fw, ew, bw], gc, gv⟩, ?_⟩
  have hcst := pairPrintCost_le _ _ _ _ _ hNM hRM hDM hcap
  omega

end NearQuarticWires.StageOutput
