import Proof.Quartic.StageCert.ChainFactorDock
import Proof.Quartic.StageCert.ChainRead
import Proof.Quartic.StageMain.ParameterGet

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells
open NearQuarticWires.StageLift

/-- `sec:params` and `lem:print`, paper/paper.tex: a serialized frequency `16G+1` determines the exact
original occurrence count by bounded integer subtraction and division. -/
def readFrequencyCount (i : Fin 46) (dst : Fin VV) : St VV MM :=
  .seq (StageMain.readParameter i atomValue)
    (.seq (.op (.sub atomValue v1))
      (.seq (setK tupleQuotient 16) (.op (.dm atomValue tupleQuotient dst tupleRemainder))))

/-- `sec:params` and `lem:print`, paper/paper.tex: actual retained frequency records yield gate counts without
rescanning the raw bank or supplying a decoded-count oracle. -/
theorem readFrequencyCount_run (C : Ctx) (p : Cells.Parameters) (i : Fin 46) (dst : Fin VV)
    (hconst : dst∉[vZ,v1,v2]) (hne : dst≠atomValue ∧ dst≠tupleQuotient ∧ dst≠tupleRemainder)
    (count : ℕ) (a : DS VV MM) (hc : Cst a)
    (hstore : a.ram parameterStore=parameterScalars p)
    (hvalue : (parameterScalars p).getD i.val 0=16*count+1)
    (hi : i.val<2^C.Wd) (hW : 5≤C.Wd) :
    Hs C (readFrequencyCount i dst) a (a.rc parameterStore+7*i.val+53) (fun z=>
      z.env dst=count ∧ z.rc parameterStore=i.val+1 ∧
      StageMain.parameterRest z=StageMain.parameterRest a ∧ Cst z ∧
      Fr a z ([t2,vJ,c0,atomValue,tupleQuotient,tupleRemainder]++[dst])) := by
  have h32 : 32≤2^C.Wd := by
    have hh := Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide) hW
    norm_num at hh
    exact hh
  unfold readFrequencyCount
  apply Hx.hs
  refine Hs.then (StageMain.readParameter_run C p i atomValue a hc hstore hi (by decide))
    (fun b ⟨bv,br,bs,bc,bfr⟩ n1 hn1=>?_)
  have bv' : b.env atomValue=16*count+1 := bv.trans hvalue
  refine Hs.then (hs_sub C atomValue v1 b (by decide) (by rw [bv',bc.one]; omega))
    (fun d hd n2 hn2=>?_)
  subst hd
  refine Hs.then (setK_spec tupleQuotient (by decide) 16 _ (by omega))
    (fun e ⟨eq,es,efr⟩ n3 hn3=>?_)
  have ev : e.env atomValue=16*count := by
    rw [efr _ (by decide)]
    simp [bv',bc.one]
  have ec : Cst e := Cst.of_fr (T := [tupleQuotient,vJ])
    (Cst.of_fr (T := [atomValue]) bc (Fr.set _ _ (by simp)) (by decide)) efr (by decide)
  refine Hs.last (hs_dm C atomValue tupleQuotient dst tupleRemainder e
    (by decide) (Ne.symm hne.1) (by decide) (Ne.symm hne.2.1) (by decide) hne.2.2
    (by rw [eq]; omega) (by rw [eq]; omega))
    (fun z hz n4 hn4=>?_)
  subst hz
  have epr : StageMain.parameterRest e=StageMain.parameterRest b := by
    have hs := Same.of_sh es
    simp only [StageMain.parameterRest,hs.ip,hs.out,hs.ram,hs.rc,hs.kin,hs.kout,hs.kc,DS.set]
  have erc : e.rc=b.rc := congrArg (fun q=>q.2.2.2.1) es
  refine ⟨⟨?_,?_,?_,?_,?_⟩,?_⟩
  · rw [DS.set_env_ne _ _ hne.2.2,DS.set_env_self,ev,eq]
    omega
  · simpa only [DS.set_rc] using (congrFun erc parameterStore).trans br
  · simpa only [StageMain.parameterRest,DS.set] using epr.trans bs
  · exact Cst.of_fr (T := [dst,tupleRemainder]) ec
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))) (by
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hconst ⊢
        exact ⟨⟨Ne.symm hconst.1,by decide⟩,⟨Ne.symm hconst.2.1,by decide⟩,
          ⟨Ne.symm hconst.2.2,by decide⟩⟩)
  · exact (bfr.weaken (by
        intro x hx
        simp only [List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢
        tauto)).trans ((Fr.set _ _ (by simp)).trans ((efr.weaken (by simp)).trans
          ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))))
  · omega

end NearQuarticWires.StageCert.Tokens
