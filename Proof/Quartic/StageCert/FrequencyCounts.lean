import Proof.Quartic.StageCert.FrequencyCount

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearQuarticWires.StageLift

/-- `sec:params`, paper/paper.tex: the first
original occurrence count is retained for exact circuit-bank selection. -/
def firstGateCount : Fin VV := ⟨127,by decide⟩

/-- `sec:params`, paper/paper.tex: the literal first
frequency record has the canonical count-encoding used by the source loader. -/
theorem retained_first_frequency (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) :
    (parameterScalars p).getD 14 0=16*c.first.gates.length+1 := by
  change p.omega1=16*c.first.gates.length+1
  rw [hs.omega1_eq,hs.m_eq]
  rfl

/-- `sec:params`, paper/paper.tex: the second
frequency record encodes zero counts correctly as well as nonempty banks. -/
theorem retained_second_frequency (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) :
    (parameterScalars p).getD 15 0=16*c.second.gates.length+1 := by
  change p.omega2=16*c.second.gates.length+1
  rw [hs.omega2_eq,hs.m_eq]
  rfl

/-- `sec:params` and `lem:print`, paper/paper.tex: both original occurrence counts are loaded from actual
retained frequency fields; the common atom stride is their exact sum. -/
def loadOccurrenceCounts : St VV MM :=
  .seq (readFrequencyCount ⟨14,by decide⟩ firstGateCount)
    (.seq (readFrequencyCount ⟨15,by decide⟩ atomCount) (.op (.add atomCount firstGateCount)))

/-- `sec:params`, `lem:print` and `prop:time`, paper/paper.tex: the source atom stride and
first-bank boundary are produced by actual parameter reads and exact
bounded arithmetic, with no original-bank count oracle. -/
theorem loadOccurrenceCounts_run (C : Ctx) (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p)
    (a : DS VV MM) (hc : Cst a) (hstore : a.ram parameterStore=parameterScalars p)
    (hW : 5≤C.Wd) (hfit : c.first.gates.length+c.second.gates.length<2^C.Wd) :
    Hs C loadOccurrenceCounts a (a.rc parameterStore+327) (fun z=>
      z.env firstGateCount=c.first.gates.length ∧
      z.env atomCount=c.first.gates.length+c.second.gates.length ∧
      z.rc parameterStore=16 ∧ StageMain.parameterRest z=StageMain.parameterRest a ∧
      Cst z ∧ Fr a z [t2,vJ,c0,atomValue,tupleQuotient,tupleRemainder,firstGateCount,atomCount]) := by
  have h32 : 32≤2^C.Wd := by
    have hh := Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide) hW
    norm_num at hh
    exact hh
  unfold loadOccurrenceCounts
  apply Hx.hs
  refine Hs.then (readFrequencyCount_run C p ⟨14,by decide⟩ firstGateCount (by decide) (by decide)
    c.first.gates.length a hc hstore (retained_first_frequency c hs)
    (by change 14<2^C.Wd; omega) hW)
    (fun b ⟨bg,br,bs,bc,bfr⟩ n1 hn1=>?_)
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
  refine Hs.then (readFrequencyCount_run C p ⟨15,by decide⟩ atomCount (by decide) (by decide)
    c.second.gates.length b bc (by rw [bram]; exact hstore)
    (retained_second_frequency c hs) (by change 15<2^C.Wd; omega) hW)
    (fun d ⟨dg,dr,ds,dc,dfr⟩ n2 hn2=>?_)
  have df : d.env firstGateCount=c.first.gates.length := (dfr _ (by decide)).trans bg
  refine Hs.last (hs_add C atomCount firstGateCount d (by decide) (by rw [dg,df]; omega))
    (fun z hz n3 hn3=>?_)
  subst hz
  refine ⟨⟨?_,?_,dr,ds.trans bs,?_,?_⟩,?_⟩
  · rw [DS.set_env_ne _ _ (by decide)]
    exact df
  · simp only [DS.set_env_self,dg,df]
    omega
  · exact Cst.of_fr (T := [atomCount]) dc (Fr.set _ _ (by simp)) (by decide)
  · exact (bfr.weaken (by decide)).trans ((dfr.weaken (by decide)).trans (Fr.set _ _ (by simp)))
  · rw [br] at hn2
    change n1≤a.rc parameterStore+7*14+53 at hn1
    change n2≤15+7*15+53 at hn2
    omega

end NearQuarticWires.StageCert.Tokens
