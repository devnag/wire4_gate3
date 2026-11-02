import Proof.CaseAnalysis.FinalParameters

/-! The validity tolerance is chosen before supplier accuracy.
`constants` is fixed before `delta`. The earlier choice `delta := 1/4`
does not meet `honest_estimates_pass` in
`Proof/Hierarchy/CompetitorSourceCompleteness.lean`: its hypothesis is
`honestError ≤ zeta constants`, whereas `EncodesSym` and `EncodesThr`
only supply `honestError ≤ delta`; see
`Proof/CaseAnalysis/FinalCompletenessDyadic.lean`.

Taking `delta := zeta constants` closes that inequality directly.
`constant_copies` accepts any rational in `(0, 1/2]` and returns a larger
fixed XOR power if necessary. See `exists_closureParametersZeta` below. 


-/
namespace NearCubicWires.RepairSource.CloseoutFinal
open SourceInterfaces RepairRepresentation CloseoutLanguage CloseoutParameters
open CompetitorRationalGap
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- Every parameter field of `PhysicalWitness`, at one fixed gamma, with the
validity tolerance already fixed. `delta = zeta constants` is what the
completeness chain needs. -/
theorem exists_closureParametersZeta (sources : EightSources)
    (constants : Constants (selectedPCPP sources)) (gamma : ℝ) (hg : 0 < gamma) :
    ∃ (degree copies clauseDegree : Nat),
      17*sources.amplification.stvExponent ≤ degree ∧
      (selectedAmplifier sources.amplification degree).arityCoefficient ≤ copies ∧
      1 ≤ clauseDegree ∧ ClauseReady sources degree clauseDegree ∧
      0 < zeta constants ∧ zeta constants < 1/2 ∧
      xorEpsilon ((zeta constants : ℚ) : ℝ) copies < gamma := by
  have hpos : 0 < zeta constants := zeta_positive constants
  have hhalfR : ((zeta constants : ℚ) : ℝ) < 1/2 := radius_lt_half constants
  have hhalf : zeta constants < 1/2 := by
    have h : ((zeta constants : ℚ) : ℝ) < ((1/2 : ℚ) : ℝ) := by push_cast; exact hhalfR
    exact_mod_cast h
  obtain ⟨copies, _hpos, hcover, heps⟩ :=
    constant_copies (zeta constants) hpos (le_of_lt hhalfR) gamma hg
      (selectedAmplifier sources.amplification (17*sources.amplification.stvExponent)).arityCoefficient
  obtain ⟨clauseDegree, hD, hready⟩ :=
    exists_clauseReady sources (17*sources.amplification.stvExponent)
  exact ⟨17*sources.amplification.stvExponent, copies, clauseDegree,
    Nat.le_refl _, hcover, hD, hready, hpos, hhalf, heps⟩

end NearCubicWires.RepairSource.CloseoutFinal
