import Proof.Quartic.StageCert.StructuralPhysical

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicGates.Close.Interfaces

/-- `imp:partition`, paper/paper.tex: an actual sampler
coordinate has the identical integer code in the canonical star-pattern radix. -/
def builderPatternIndex (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (i : Fin hs.seedParameters.N) :
    Fin (((Builder.star c hs).b+1)^((Builder.star c hs).r/2)) :=
  ⟨i.val,by
    simpa only [Builder.seedN_eq_patternCodes c hs,
      ←NearCubicWires.WireExponent3_5.SeedFix.callN_eq] using i.isLt⟩

/-- `imp:partition`, paper/paper.tex: the exact numeric
decoder returns the literal original `Builder.pattern`, including its order. -/
theorem builder_pattern_eq_numeric (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (i : Fin hs.seedParameters.N) :
    Builder.pattern c hs i=
      (errorsEquiv (Builder.star c hs)).symm (builderPatternIndex c hs i) := by
  apply (NearCubicWires.WireExponent3_5.SeedFix.callEqv (Builder.star c hs)).injective
  change (NearCubicWires.WireExponent3_5.SeedFix.callEqv (Builder.star c hs))
    ((Builder.patternEquiv c hs) i)=_
  rw [Builder.patternEquiv,Equiv.trans_apply,Equiv.apply_symm_apply]
  simp only [NearCubicWires.WireExponent3_5.SeedFix.callEqv,
    Equiv.trans_apply,Equiv.apply_symm_apply]
  apply Fin.ext
  rfl

/-- `def:mask`, paper/paper.tex: the exact original
column mask is the numeric source mask computed by `structuralProgram`.
The statement applies to every witness and every original column. -/
theorem builder_structural_eq_numeric (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p)
    (w : List Bool) (z : Fin (2^(c.n-p.k))) (u v : Fin hs.seedParameters.N) :
    (Builder.columnData c hs w z).structural (u,v)=
      Mask.structuralMask ((Builder.star c hs).flipSet (Builder.star c hs).leftBlock)
        ((Builder.star c hs).flipSet (Builder.star c hs).rightBlock)
        (Mask.heavyCoordinates (fun i=>Incidence.sourceDegree c i.val) p.dstar)
        ((errorsEquiv (Builder.star c hs)).symm (builderPatternIndex c hs u))
        ((errorsEquiv (Builder.star c hs)).symm (builderPatternIndex c hs v)) := by
  have hd : (fun i : Fin (Builder.star c hs).n=>Incidence.sourceDegree c i.val)=
      Cells.incidence (Builder.allGates c) := by
    funext i
    exact Incidence.sourceDegree_eq c i
  rw [hd]
  change Mask.structuralMask _ _ _ (Builder.pattern c hs u) (Builder.pattern c hs v)=_
  rw [builder_pattern_eq_numeric,builder_pattern_eq_numeric]
  rfl

end NearQuarticWires.StageCert
