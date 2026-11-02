import Proof.Quartic.StageCert.TupleProduct

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the exact tuple population `G^a` is computed and retained
in a binary register, independently of every tuple address. -/
def tupleTotal : Fin VV := ⟨119,by decide⟩

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: a power step multiplies the current exact tuple population
by the original occurrence count. -/
def tuplePowerStep : St VV MM :=
  .seq (.op (.mul tupleTotal atomCount tupleQuotient)) (.op (.copy tupleTotal tupleQuotient))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: dynamic-degree tuple populations use an actual bounded
binary multiplication loop, with the unit case at degree zero. -/
def computeTupleTotal : St VV MM :=
  .seq (.op (.copy tupleTotal v1)) (forS tuplePosition newtonIndex tuplePowerStep)

/-- `lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: the exact number of bounded
tuples is physically computed in linearly many binary operations. -/
theorem computeTupleTotal_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (G degree : ℕ) (hG : 1≤G) (hb : a.env atomCount=G) (hd : a.env newtonIndex=degree)
    (hfit : G^degree<2^C.Wd) (hdfit : degree<2^C.Wd) :
    Hs C computeTupleTotal a (7*degree+6) (fun z=>z.env tupleTotal=G^degree ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [tuplePosition,tupleTotal,tupleQuotient]) := by
  unfold computeTupleTotal
  refine (Hs.seq (t1 := 1) (t2 := 7*degree+4)
    (hs_copy C tupleTotal v1 a (by decide)) ?_).mono (by omega) (fun _ h=>h)
  rintro b rfl
  let I : ℕ→DS VV MM→Prop := fun i b=>
    b.env tupleTotal=G^i ∧ b.sh=a.sh ∧ Cst b ∧ Fr a b [tuplePosition,tupleTotal,tupleQuotient]
  have hset : ∀ i b v,I i b→I i (b.set tuplePosition v) := by
    rintro i b v ⟨bt,bs,bc,bf⟩
    exact ⟨by simpa only [DS.set_env_ne _ _ (by decide : tupleTotal≠tuplePosition)] using bt,
      bs,Cst.of_fr (T := [tuplePosition]) bc (Fr.set _ _ (by simp)) (by decide),
      bf.trans (Fr.set _ _ (by simp))⟩
  have h0 : I 0 (a.set tupleTotal (a.env v1)) := by
    exact ⟨by simp [hc.one],rfl,
      Cst.of_fr (T := [tupleTotal]) hc (Fr.set _ _ (by simp)) (by decide),Fr.set _ _ (by simp)⟩
  refine (forS_spec' (C := C) tuplePosition newtonIndex (by decide) tuplePowerStep
    (a.set tupleTotal (a.env v1)) degree hdfit I 3 hset h0
    (by rw [DS.set_env_ne _ _ (by decide)]; exact hd) ?_).mono (by omega) ?_
  · intro i hi b ⟨bt,bs,bc,bfr⟩ bi bn
    have bG : b.env atomCount=G := (bfr _ (by decide)).trans hb
    have hnext : G^i*G<2^C.Wd := by
      rw [←pow_succ]
      exact (Nat.pow_le_pow_right hG (by omega : i+1≤degree)).trans_lt hfit
    unfold tuplePowerStep
    refine Hs.seq (t1 := 1) (t2 := 1)
      (hs_mul C tupleTotal atomCount tupleQuotient b (by decide) (by decide) (by decide)
        (by rw [bt,bG]; exact hnext)) ?_
    rintro d rfl
    refine (hs_copy C tupleTotal tupleQuotient _ (by decide)).mono le_rfl ?_
    rintro z rfl
    refine ⟨⟨?_,bs,?_,?_⟩,?_,?_⟩
    · simp only [DS.set_env_self]
      rw [bt,bG,pow_succ]
    · exact Cst.of_fr (T := [tupleQuotient,tupleTotal]) bc
        ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))) (by decide)
    · exact bfr.trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))
    · vsimp [bi]
    · vsimp [bn]
  · rintro z ⟨hz,_,_⟩
    exact hz

end NearQuarticWires.StageCert.Tokens
