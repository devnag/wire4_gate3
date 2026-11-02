import Proof.Quartic.StageCert.MomentExponent
import Proof.Quartic.StageLift.AritySource

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells
open StageLift

/-- `lem:print`, paper/paper.tex: compute the
literal exact-CERT degree 16 Xmax + 8 k from the actual parameter
store, without the distinct Greedy residue degree. -/
def computeMomentDegree : St VV MM :=
  .seq (StageMain.readParameter ⟨12,by decide⟩ degreeInput)
    (.seq (StageMain.readParameter ⟨6,by decide⟩ selectionStart)
      (.seq (setK degreeFactor 16)
        (.seq (.op (.mul degreeInput degreeFactor degreeVar))
          (.seq prepareWalkExponent (.op (.add degreeVar momentExponent))))))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual degree field is produced by two paid
record reads and bounded binary arithmetic, preserving every source byte. -/
theorem computeMomentDegree_run (C : Ctx) (p : Cells.Parameters)
    (a : DS VV MM) (hc : Cst a) (hparams : a.ram parameterStore=parameterScalars p)
    (hW : 5≤C.Wd) (hfit : 16*p.Xmax+8*p.k<2^C.Wd) :
    Hs C computeMomentDegree a (a.rc parameterStore+250) (fun z=>
      z.env degreeVar=16*p.Xmax+8*p.k ∧ z.rc parameterStore=7 ∧
      StageMain.parameterRest z=StageMain.parameterRest a ∧ Cst z ∧
      Fr a z [t2,vJ,c0,degreeInput,selectionStart,degreeFactor,degreeVar,momentExponent]) := by
  have h32 : 32≤2^C.Wd := by
    have hh := Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hW
    norm_num at hh
    exact hh
  unfold computeMomentDegree
  apply Hx.hs
  refine Hs.then (StageMain.readParameter_run C p ⟨12,by decide⟩ degreeInput a hc hparams
    (by change 12<2^C.Wd; omega) (by decide))
    (fun b ⟨bx,br,bs,bc,bf⟩ n1 hn1=>?_)
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
  refine Hs.then (StageMain.readParameter_run C p ⟨6,by decide⟩ selectionStart b bc
    (by rw [bram]; exact hparams) (by change 6<2^C.Wd; omega) (by decide))
    (fun d ⟨dk,dr,ds,dc,df⟩ n2 hn2=>?_)
  refine Hs.then (setK_spec degreeFactor (by decide) 16 d (by omega))
    (fun e ⟨ef,es,efr⟩ n3 hn3=>?_)
  have ec : Cst e := Cst.of_fr dc efr (by decide)
  have ex : e.env degreeInput=p.Xmax :=
    (efr _ (by decide)).trans ((df _ (by decide)).trans bx)
  have ek : e.env selectionStart=p.k := (efr _ (by decide)).trans dk
  refine Hs.then (hs_mul C degreeInput degreeFactor degreeVar e
    (by decide) (by decide) (by decide) (by rw [ex,ef]; omega))
    (fun f hf n4 hn4=>?_)
  subst hf
  let f := e.set degreeVar (e.env degreeInput*e.env degreeFactor)
  have fc : Cst f := Cst.of_fr ec (Fr.set _ _ (T := [degreeVar]) (by simp)) (by decide)
  have fd : f.env degreeVar=16*p.Xmax := by change e.env degreeInput*e.env degreeFactor=_; rw [ex,ef]; omega
  refine Hs.then (prepareWalkExponent_run C p.k f fc
    (by change e.env selectionStart=p.k; exact ek) (by omega))
    (fun q ⟨qm,qs,qc,qf⟩ n5 hn5=>?_)
  have qd : q.env degreeVar=16*p.Xmax := (qf _ (by decide)).trans fd
  refine Hs.last (hs_add C degreeVar momentExponent q (by decide) (by rw [qd,qm]; exact hfit))
    (fun z hz n6 hn6=>?_)
  subst hz
  have hf : Fr a (q.set degreeVar (q.env degreeVar+q.env momentExponent))
      [t2,vJ,c0,degreeInput,selectionStart,degreeFactor,degreeVar,momentExponent] :=
    (bf.weaken (by decide)).trans ((df.weaken (by decide)).trans
      ((efr.weaken (by decide)).trans ((Fr.set _ _ (by simp)).trans
        ((qf.weaken (by decide)).trans (Fr.set _ _ (by simp))))))
  have qrc : q.rc=d.rc := by
    have eqrc : e.rc=d.rc := congrArg (fun q=>q.2.2.2.1) es
    have fqrc : q.rc=f.rc := congrArg (fun q=>q.2.2.2.1) qs
    exact fqrc.trans eqrc
  refine ⟨⟨by simp only [DS.set_env_self,qd,qm],(congrFun qrc parameterStore).trans dr,
    ?_,Cst.of_fr hc hf (by decide),hf⟩,?_⟩
  · have erest : StageMain.parameterRest e=StageMain.parameterRest d := by
      exact congrArg (fun q=>(q.1,q.2.1,q.2.2.1,Function.update q.2.2.2.1 parameterStore 0,
        q.2.2.2.2.1,q.2.2.2.2.2.1,q.2.2.2.2.2.2)) es
    have qrest : StageMain.parameterRest q=StageMain.parameterRest e :=
      congrArg (fun q=>(q.1,q.2.1,q.2.2.1,Function.update q.2.2.2.1 parameterStore 0,
        q.2.2.2.2.1,q.2.2.2.2.2.1,q.2.2.2.2.2.2)) qs
    exact qrest.trans (erest.trans (ds.trans bs))
  · change n1≤a.rc parameterStore+7*12+13 at hn1
    change n2≤b.rc parameterStore+7*6+13 at hn2
    rw [br] at hn2
    change n2≤13+7*6+13 at hn2
    norm_num at hn3
    omega

end NearQuarticWires.StageCert.Tokens
