import Proof.Quartic.StageCert.PatternPhysical
import Proof.Gates.Dispatch.WitnessB
import Proof.Gates.Dispatch.Setup

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Dispatch

/-- The witness of `sec:algorithm`, paper/paper.tex:
the exact source offset of its retained, framed prefix. -/
def sourceWitnessBase : Fin VV := ⟨120,by decide⟩
/-- The witness of `sec:algorithm`, paper/paper.tex:
the literal W1, W2 or W3 bit index. -/
def sourceWitnessIndex : Fin VV := ⟨121,by decide⟩
/-- The witness of `sec:algorithm`, paper/paper.tex:
the exact data-bit position inside the retained framed source word. -/
def sourceWitnessTarget : Fin VV := ⟨122,by decide⟩
/-- The witness of `sec:algorithm`, paper/paper.tex:
one actual retained witness bit as a natural zero or one. -/
def sourceWitnessResult : Fin VV := ⟨123,by decide⟩

/-- The witness of `sec:algorithm`, paper/paper.tex:
the source data-bit address is `base+2*index+1`. -/
def witnessAddress : St VV := .seq (.op (.copy sourceWitnessTarget sourceWitnessIndex))
  (.seq (.op (.shl sourceWitnessTarget))
    (.seq (.op (.inc sourceWitnessTarget)) (.op (.add sourceWitnessTarget sourceWitnessBase))))

/-- The witness of `sec:algorithm`, paper/paper.tex:
the framed witness-bit address is computed by actual bounded arithmetic. -/
theorem witnessAddress_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (hfit : a.env sourceWitnessBase+2*a.env sourceWitnessIndex+1<2^C.Wd) :
    Hs C witnessAddress a 7 (fun z =>
      z.env sourceWitnessTarget=a.env sourceWitnessBase+2*a.env sourceWitnessIndex+1 ∧
      z.cp=a.cp ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z [sourceWitnessTarget]) := by
  unfold witnessAddress
  refine Hs.seq (t1 := 1) (t2 := 5)
    (hs_copy C sourceWitnessTarget sourceWitnessIndex a (by decide)) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_shl C sourceWitnessTarget _ (by simp only [DS.set_env_self]; omega)) ?_
  rintro d rfl
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_inc C sourceWitnessTarget _ (by simp only [DS.set_env_self]; omega)) ?_
  rintro e rfl
  refine (hs_add C sourceWitnessTarget sourceWitnessBase _ (by decide)
    (by vsimp [sourceWitnessTarget]; omega)).mono le_rfl ?_
  rintro z rfl
  refine ⟨?_,rfl,rfl,rfl,?_,?_⟩
  · vsimp [sourceWitnessTarget,sourceWitnessBase,sourceWitnessIndex]
    omega
  · exact ⟨by vsimp [sourceWitnessTarget,sourceWitnessBase,sourceWitnessIndex,hc.z],
      by vsimp [sourceWitnessTarget,sourceWitnessBase,sourceWitnessIndex,hc.one],
      by vsimp [sourceWitnessTarget,sourceWitnessBase,sourceWitnessIndex,hc.two],
      by vsimp [sourceWitnessTarget,sourceWitnessBase,sourceWitnessIndex,hc.pos]⟩
  · exact (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))))

end NearQuarticWires.StageCert
