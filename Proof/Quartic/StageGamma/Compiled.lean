import Proof.Quartic.StageGamma.CompleteBody
import Proof.Quartic.StageGamma.ContextReserve

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.PrefixProg

/-- `prop:time`, paper/paper.tex: the actual
Gaussian compiler reserves polynomial-width input and work streams from
the ORIGINAL degree header, never a padded field-label enumeration. -/
def gammaSizes : Sz := ⟨256, 1, 1000000, 1, 10 ^ 15, 6⟩

/-- `cor:conditional`, paper/paper.tex: the retained
source has exactly the same ORIGINAL degree header as its official request. -/
theorem cachedRequest_leadOnes (request : Machine.GammaRequest) :
    leadOnes (cachedRequestWord request) = natBitLength request.parameters.ell := by
  unfold cachedRequestWord Machine.gammaRequestWord
  simp only [List.append_assoc]
  exact leadOnes_natWord _ _

/-- `prop:time`, paper/paper.tex: actual binary
width, source reserve and Gaussian call reserve are sufficient for the
entire original coefficient program, including every signed partial sum. -/
theorem gammaSizes_sufficient (request : Machine.GammaRequest) :
    4 * Cycle.seedLength request.parameters + 10 ≤
        gammaSizes.W (leadOnes (cachedRequestWord request)) ∧
      gaussInputReserve request ≤ gammaSizes.Lk (leadOnes (cachedRequestWord request)) ∧
      gaussWorkReserve request ≤ gammaSizes.Bk (leadOnes (cachedRequestWord request)) := by
  have hp : request.parameters.ell + 1 ≤ 2 ^ natBitLength request.parameters.ell := by
    have hh := lt_natBitLength request.parameters.ell
    omega
  rw [cachedRequest_leadOnes]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [gammaSizes, Sz.W, Cycle.seedLength]
    simp only [one_mul]
    omega
  · dsimp [gaussInputReserve, gammaSizes, Sz.Lk, Cycle.seedLength]
    simp only [one_mul]
    omega
  · dsimp [gaussWorkReserve, gammaSizes, Sz.Bk]
    rw [show 6 * natBitLength request.parameters.ell =
      natBitLength request.parameters.ell * 6 by omega, pow_mul]
    have hb : Cycle.seedLength request.parameters + 9 ≤
        9 * (2 ^ natBitLength request.parameters.ell) := by
      dsimp [Cycle.seedLength]
      omega
    calc
      _ ≤ 1000000 * (9 * 2 ^ natBitLength request.parameters.ell) ^ 6 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
      _ ≤ _ := by rw [mul_pow]; norm_num; omega

/-- `prop:time`, paper/paper.tex: the actual source
execution charge includes the compiler's full larger per-call reserves. -/
noncomputable def compiledGammaSourceCost (request : Machine.GammaRequest) : ℕ :=
  let L := leadOnes (cachedRequestWord request)
  gammaCachedBodyCost request (gammaSizes.W L) *
    (1 + gammaSizes.Lk L + gammaSizes.Bk L)

/-- `prop:time`, paper/paper.tex: physical setup,
ordinary compilation, every Gaussian reset and final output rewinding are
all included in this concrete cold cached-source budget. -/
noncomputable def compiledGammaCost (request : Machine.GammaRequest) : ℕ :=
  langBudget compactGaussCallee gammaSizes VV MM (cachedRequestWord request)
    (compiledGammaSourceCost request)

/-- `cor:conditional` and `prop:time`, paper/paper.tex: one genuine cold retained-source WordFunction computes the
complete ORIGINAL signed conditional coefficient using exactly its true
radix census, a cached field, physical Gaussian calls and canonical output. -/
noncomputable def cachedGammaWordFunction :
    WordFunction Machine.GammaRequest cachedRequestWord
      (fun request => NearCubicGates.Close.Interfaces.intWord (Machine.gammaTarget request))
      compiledGammaCost :=
  wordFunction_of_lang cachedRequestWord
    (fun request => NearCubicGates.Close.Interfaces.intWord (Machine.gammaTarget request))
    compactGaussCallee gammaSizes gammaCachedBody compiledGammaSourceCost (by
      intro request
      let L := leadOnes (cachedRequestWord request)
      let width := gammaSizes.W L
      obtain ⟨hw, hL, hB⟩ := gammaSizes_sufficient request
      obtain ⟨b, n, hex, hn, hout⟩ := gammaCachedBody_run request width hw
      obtain ⟨n', hex', hn'⟩ := Ex.enlarge_reserves width (cachedRequestWord request)
        (gaussInputReserve request) (gaussWorkReserve request)
        (gammaSizes.Lk L) (gammaSizes.Bk L) hL hB hex
      refine ⟨b, n', hex', hout, ?_⟩
      exact hn'.trans (Nat.mul_le_mul_right _ hn)) (by
        intro request
        have hh := (gammaSizes_sufficient request).1
        omega)

/-- `prop:time`, paper/paper.tex: the ORIGINAL
source stage pays once-only cache setup and the complete compiled
coefficient computation, including the physical framed handoff. -/
noncomputable def gammaBudget (request : Machine.GammaRequest) : ℕ :=
  4 * cachedRequestBudget request + 4 * compiledGammaCost request + 12

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the requested ORIGINAL-codec Gamma function is an actual
cold ordinary machine, with no supplied cache, Gaussian bank, hidden label
padding, arbitrary decoder, or repeated primitive-field search. -/
noncomputable def gammaWordFunction :
    WordFunction Machine.GammaRequest Machine.gammaRequestWord
      (fun request => NearCubicGates.Close.Interfaces.intWord (Machine.gammaTarget request)) gammaBudget :=
  NearQuarticWires.Program.WordFunction.pipe cachedRequestWordFunction cachedGammaWordFunction

end NearQuarticWires.StageGamma
