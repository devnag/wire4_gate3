import Proof.Quartic.StageCert.EdgePatterns

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `def:mask` and `lem:print`, paper/paper.tex: write the actual original structural Boolean after its
concrete callee reply has been decoded. -/
def emitStructuralFlag : St VV MM := emitB .emit maskStructural

/-- `def:mask` and `prop:time`, paper/paper.tex: writing the decoded Boolean preserves every retained
source word, arithmetic register and callee stream. -/
theorem emitStructuralFlag_run (C : Ctx) (flag : Bool) (a : DS VV MM) (hc : Cst a)
    (hflag : a.env maskStructural=flag.toNat) :
    Hs C emitStructuralFlag a 2 (fun z=>
      z.out=a.out++[flag] ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      z.env=a.env ∧ Cst z) := by
  refine (emitB_spec (snkO C) maskStructural (by decide) a hc trivial).mono le_rfl ?_
  rintro z ⟨zo,zs,ze⟩
  have hb : decide (a.env maskStructural=1)=flag := by cases flag <;> simp [hflag]
  refine ⟨?_,zs,ze,?_⟩
  · change z.out=a.out++[decide (a.env maskStructural=1)] at zo
    simpa only [hb] using zo
  · exact ⟨(congrFun ze vZ).trans hc.z,(congrFun ze v1).trans hc.one,
      (congrFun ze v2).trans hc.two⟩

end NearQuarticWires.StageCert.Tokens
