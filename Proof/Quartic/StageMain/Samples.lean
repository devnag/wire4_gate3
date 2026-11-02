import Proof.Wire_3_5.FinalPassHashCell
import Proof.Wire_3_5.SamplerCond

/-!
# Physical evaluation of the eight-coefficient sampler

`imp:seed`, paper/paper.tex, evaluates a degree-seven
polynomial at each label for the choice h = 4. Step 4 of `sec:algorithm`, uses the resulting sample positions. The word-tape
Horner loop below evaluates exactly that polynomial, retains its seed
records and modulus, and has a quadratic cost in the field degree.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5
open FinalPass FinalPass.Hash4 FinalPass.Tm

/-- Coefficient records in the high-to-low order read by Horner's rule. -/
def sampleCoefficients (ell seed : ℕ) : List ℕ :=
  coefsRev (fun i : Fin 8 => Sampler.seedCoeff ell seed i)

@[simp] theorem sampleCoefficients_length (ell seed : ℕ) :
    (sampleCoefficients ell seed).length = 8 := by
  simp [sampleCoefficients, coefsRev]

theorem sampleHorner_eq_gen (p ell seed label : ℕ)
    (hp : GF.ModulusOk p ell) (he : 1 ≤ ell) (hl : label < 2 ^ ell) :
    (sampleCoefficients ell seed).foldl (hornerStep p ell label) 0 =
      JoinElimination.gen p ell 8 seed label := by
  unfold sampleCoefficients
  rw [hornerBits_fold]
  obtain ⟨hb, hv⟩ := hornerBits_spec p ell hp label hl 8
    (fun i : Fin 8 => Sampler.seedCoeff ell seed i) (fun _ => Sampler.seedCoeff_lt _ _ _)
  obtain ⟨gb, gv⟩ := Sampler.gen_spec p ell seed label hp he hl 8
  apply GF.rep_injOn p ell _ _ hp hb gb
  rw [hv]
  exact (Fin.sum_univ_eq_sum_range _ 8).trans gv.symm

theorem sampleKernel_spec (cap p ell seed label : ℕ)
    (hp : GF.ModulusOk p ell) (he : 1 ≤ ell) (hl : label < 2 ^ ell)
    (hc : 18 * ell + 19 ≤ cap) (a : HState)
    (ha : HReady p ell label (sampleCoefficients ell seed) a) :
    ∃ b, WExec cap hornerW a b (hornerCost ell 8) ∧
      HReady p ell label (sampleCoefficients ell seed) b ∧
      b.st (5 : Fin 8) = frame (binary ell (JoinElimination.gen p ell 8 seed label)) ∧
      WFrame hornS hornR a b := by
  have hh : (seedWord ell (sampleCoefficients ell seed)).length + 2 * ell + 2 ≤ cap := by
    rw [seedWord_length, sampleCoefficients_length]
    omega
  obtain ⟨b, hb, hr, ho, hf⟩ := hornerW_spec cap p ell label (sampleCoefficients ell seed) he hh a ha
  refine ⟨b, by simpa using hb, hr, ?_, hf⟩
  simpa only [sampleHorner_eq_gen p ell seed label hp he hl] using ho

theorem sampleKernel_cost (ell : ℕ) : hornerCost ell 8 ≤ 2000 * (ell + 1) ^ 2 := by
  unfold hornerCost recCost mulStepCost
  nlinarith

end NearQuarticWires.StageMain
