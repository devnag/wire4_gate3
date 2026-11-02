import Proof.Quartic.StageCert.PopulationPrefix
import Proof.Quartic.StageCert.StructuralBuilder

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain

/-- `def:mask`, paper/paper.tex: the numeric original
occurrence-prefix sum equals the literal finite sum over occurrence labels. -/
theorem populationPrefix_eq_sum {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (points : Fin 4→ℕ) (bits : List Bool) (index : ℕ) :
    populationPrefix gs points bits index gs.length=
      ∑i : Fin gs.length,if Algorithm.witnessBit bits (index+i.val) then
        gateMagnitude gs[i.val] points else 0 := by
  have he : ((List.range gs.length).map fun j=>if hj : j<gs.length then
      if Algorithm.witnessBit bits (index+j) then gateMagnitude gs[j] points else 0
      else 0)=List.ofFn (fun i : Fin gs.length=>
        if Algorithm.witnessBit bits (index+i.val) then gateMagnitude gs[i.val] points else 0) := by
    apply List.ext_getElem
    · simp
    · intro j hj _
      have h : j<gs.length := by simpa using hj
      simp [h]
  unfold populationPrefix
  rw [he,Fin.sum_ofFn]

/-- `sec:cells`, paper/paper.tex: the raw four-corner
evaluator's magnitude is the paper's literal original mixed residual. -/
theorem gateMagnitude_eq_delta (P : StarParams) (g : NormalizedThresholdGate P.n)
    (center : BitInput P.n) (u v : P.Errors) (points : Fin 4→ℕ)
    (h0 : packedPoint P.n (points 0)=center)
    (h1 : packedPoint P.n (points 1)=xorInput center (P.errorVector P.leftBlock u))
    (h2 : packedPoint P.n (points 2)=xorInput center (P.errorVector P.rightBlock v))
    (h3 : packedPoint P.n (points 3)=P.point center u v) :
    gateMagnitude g points=(Cells.delta P g center u v).natAbs := by
  simp only [gateMagnitude,fourBitDifference,h0,h1,h2,h3,Cells.delta,mixedDifference,
    StarParams.point]

/-- `def:mask`, paper/paper.tex: the selected-population
source sum is exactly the original `Builder.columnData.X`, with every
repeated raw occurrence and every witness selection bit retained. -/
theorem builder_X_eq_populationPrefix (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (bits : List Bool)
    (z : Fin (2^(c.n-p.k))) (u v : Fin hs.seedParameters.N) (points : Fin 4→ℕ)
    (h0 : packedPoint c.n (points 0)=Builder.center c hs bits z)
    (h1 : packedPoint c.n (points 1)=xorInput (Builder.center c hs bits z)
      ((Builder.star c hs).errorVector (Builder.star c hs).leftBlock (Builder.pattern c hs u)))
    (h2 : packedPoint c.n (points 2)=xorInput (Builder.center c hs bits z)
      ((Builder.star c hs).errorVector (Builder.star c hs).rightBlock (Builder.pattern c hs v)))
    (h3 : packedPoint c.n (points 3)=(Builder.star c hs).point (Builder.center c hs bits z)
      (Builder.pattern c hs u) (Builder.pattern c hs v)) :
    (Builder.columnData c hs bits z).X (u,v)=
      populationPrefix (Builder.allGates c) points bits p.k (Builder.allGates c).length := by
  rw [populationPrefix_eq_sum]
  simp only [Builder.columnData]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Builder.selection]
  congr 1
  exact (gateMagnitude_eq_delta (Builder.star c hs) _ (Builder.center c hs bits z)
    (Builder.pattern c hs u) (Builder.pattern c hs v) points h0 h1 h2 h3).symm

end NearQuarticWires.StageCert
