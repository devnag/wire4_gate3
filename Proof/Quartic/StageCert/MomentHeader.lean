import Proof.Quartic.StageCert.MomentDegree
import Proof.Quartic.StageCert.MomentSourceRead
import Proof.Quartic.StageLift.RawHeader

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells
open StageLift
open StageRecovery

/-- `lem:print`, paper/paper.tex: the exact
packet header uses the actual degree, both original occurrence counts,
and literal modulus zero; it is distinct from any modular query header. -/
def prepareMomentHeader : St VV MM :=
  .seq computeMomentDegree (.seq computePrintArity (.op (.zero modulusVar)))

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact source header is computed from actual
retained parameter records, preserving the whole original source. -/
theorem prepareMomentHeader_run (C : Ctx) (c : NearCubicGates.Close.Interfaces.Call)
    {p : Cells.Parameters} (hs : Cells.ParameterRules (Builder.callInput c) p)
    (a : DS VV MM) (hc : Cst a) (hparams : a.ram parameterStore=parameterScalars p)
    (hW : 5≤C.Wd) (hD : 16*p.Xmax+8*p.k<2^C.Wd)
    (hV : 17*(Builder.allGates c).length<2^C.Wd) :
    Hs C prepareMomentHeader a (a.rc parameterStore+650) (fun z=>
      z.env degreeVar=16*p.Xmax+8*p.k ∧
      z.env printArityVar=17*(Builder.allGates c).length ∧ z.env modulusVar=0 ∧
      z.env atomCount=(Builder.allGates c).length ∧
      z.env firstGateCount=c.first.gates.length ∧ z.rc parameterStore=16 ∧
      StageMain.parameterRest z=StageMain.parameterRest a ∧ Cst z ∧
      Fr a z [t2,vJ,c0,degreeInput,selectionStart,degreeFactor,degreeVar,momentExponent,
        atomValue,tupleQuotient,tupleRemainder,firstGateCount,atomCount,printArityVar,modulusVar]) := by
  unfold prepareMomentHeader
  apply Hx.hs
  refine Hs.then (computeMomentDegree_run C p a hc hparams hW hD)
    (fun b ⟨bd,br,bs,bc,bf⟩ n1 hn1=>?_)
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
  refine Hs.then (computePrintArity_spec C c hs b bc (by rw [bram]; exact hparams) hW hV)
    (fun d ⟨dv,dG,dG1,dr,ds,dc,df⟩ n2 hn2=>?_)
  refine Hs.last (hs_zero C modulusVar d) (fun z hz n3 hn3=>?_)
  subst hz
  have hf : Fr a (d.set modulusVar 0)
      [t2,vJ,c0,degreeInput,selectionStart,degreeFactor,degreeVar,momentExponent,
        atomValue,tupleQuotient,tupleRemainder,firstGateCount,atomCount,printArityVar,modulusVar] :=
    (bf.weaken (by decide)).trans ((df.weaken (by decide)).trans (Fr.set _ _ (by simp)))
  refine ⟨⟨(df _ (by decide)).trans bd,dv,rfl,dG,dG1,dr,
    ds.trans bs,Cst.of_fr hc hf (by decide),hf⟩,?_⟩
  rw [br] at hn2
  change n2≤7+367 at hn2
  omega

end NearQuarticWires.StageCert.Tokens
