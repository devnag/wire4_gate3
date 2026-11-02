import Proof.Quartic.StageCert.TupleMoments

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Interfaces

/-- `imp:chain` and `sec:params`, paper/paper.tex: the actual retained factor list has precisely the active
zero-based chain-rate positions. -/
theorem retainedFactors_length (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) : p.factors.length=p.J-1 := by
  rw [hs.factors_eq]
  simp [NearCubicGates.Close.Counter.chainFactors]

/-- `imp:chain`, `eq:testE` and `lem:print`, paper/paper.tex: a physical read of the retained active
factor returns the exact rate appearing in the original digit, rather
than an assumed lookup value or recomputed rational approximation. -/
theorem retainedFactor_eq_rate (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (i : ℕ) (hi : i<p.J-1) :
    p.factors.getD i 0=(Builder.algorithmParameters c hs).rate i := by
  have hlen := retainedFactors_length c hs
  rw [List.getD_eq_getElem _ _ (by omega)]
  change p.factors[i]'(by omega)=NearCubicGates.RationalRateChain.factorRat
    (NearCubicGates.RationalRateChain.ratio
      (NearCubicGates.Close.Counter.firstRatio p.ell0 p.h p.T) i)
  simp only [hs.factors_eq,NearCubicGates.Close.Counter.chainFactors,List.getElem_map,List.getElem_range]

end NearQuarticWires.StageCert
