import Proof.Quartic.StageLiftTokens.ScoreCoefficient

/-!
# Eight signed score edges

`lem:residue` and `lem:print`, paper/paper.tex: each actual occurrence contributes its eight signed
integer edges with unit coefficient in its selected circuit.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator StageCert.Tokens

def scoreOccurrenceScratch : List (Fin VV) :=
  [linearPositive, linearNegative, vJ] ++ [cachedPositive, cachedNegative] ++ weightedEdgeScratch

def emitScoreOccurrence : St VV MM := .seq scoreCoefficient emitOccurrenceEdges

theorem emitScoreOccurrence_run (C : Ctx) (G g circuit firstCount code Batom : ℕ)
    (a : DS VV MM) (hc : Cst a) (hG : a.env atomCount = G)
    (hg : a.env atomOccurrence = g) (hgG : g < G)
    (hj : a.env selectedCircuit = circuit) (hf : a.env firstGateCount = firstCount)
    (hcode : a.env newtonTau = code) (hW : 5 ≤ C.Wd) (hindex : 17 * G < 2 ^ C.Wd)
    (hB : ∀ edge j, natBitLength (cornerRoleCode edge j * G + g) ≤ Batom)
    (hAtomFit : Batom + 2 < 2 ^ C.Wd) :
    Hs C emitScoreOccurrence a (8 * (40 + 160 * Batom + 640) + 40) (fun z =>
      z.out = a.out ++ (toks (occurrenceWalkFormula G g hgG
        (selectedSummand circuit firstCount g 1 : ℤ) code)).flatMap tokWord ∧
      (z.ip, z.ram, z.rc, z.kin, z.kout, z.kc) = (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst z ∧ Fr a z scoreOccurrenceScratch) := by
  have hsmall : 1 + 2 < 2 ^ C.Wd := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hW
    norm_num only [Nat.reducePow] at hh
    omega
  have hcoef : natBitLength ((((selectedSummand circuit firstCount g 1 : ℕ) : ℤ) - 0).natAbs) ≤ 1 := by
    unfold selectedSummand
    split_ifs <;> decide
  unfold emitScoreOccurrence
  apply Hx.hs
  refine Hs.then (scoreCoefficient_run C circuit firstCount g a hc hj hf hg)
    (fun b ⟨hbp,hbn,hbsh,hbc,hbfr⟩ n1 hn1 => ?_)
  refine Hs.last (emitOccurrenceEdges_run C G g (selectedSummand circuit firstCount g 1) 0 code 1 Batom b hbc
    ((hbfr _ (by decide)).trans hG) ((hbfr _ (by decide)).trans hg) hgG hbp hbn
    ((hbfr _ (by decide)).trans hcode) hW hindex hB hAtomFit hcoef hsmall)
    (fun z ⟨hzo,hzrest,hzc,hzfr⟩ n2 hn2 => ?_)
  have hs := Same.of_sh hbsh
  refine ⟨⟨?_, ?_, hzc, (hbfr.weaken (by decide)).trans (hzfr.weaken (by
    intro y hy
    simp only [scoreOccurrenceScratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hy ⊢
    tauto))⟩,?_⟩
  · simpa only [Nat.cast_zero, sub_zero, hs.out] using hzo
  · exact hzrest.trans (by rw [hs.ip, hs.ram, hs.rc, hs.kin, hs.kout, hs.kc])
  · omega

end NearQuarticWires.StageLiftTokens
