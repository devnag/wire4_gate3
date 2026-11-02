import Proof.Quartic.StageCert.PatternStep

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearQuarticWires.StagePrep

/-- `def:mask`, paper/paper.tex: the first `count`
least-significant error digits avoid all heavy original coordinates. -/
def prefixNonheavy (c : Call) (cut b offset code : ℕ) : ℕ→Prop
  | 0 => True
  | j+1 => prefixNonheavy c cut b offset code j ∧
      digitNonheavy c cut b (offset+j) (code/(b+1)^j%(b+1))

instance (c : Call) (cut b offset code count : ℕ) :
    Decidable (prefixNonheavy c cut b offset code count) := by
  induction count with
  | zero => exact isTrue trivial
  | succ j ih =>
    change Decidable (prefixNonheavy c cut b offset code j ∧ _)
    exact @instDecidableAnd _ _ ih inferInstance

/-- `def:mask`, paper/paper.tex: the original block
endpoint controls one exact finite side scan. -/
def patternLoop : St VV := .loop (.lt patternBlock patternEnd) patternStep

/-- `def:mask` and `prop:time`, paper/paper.tex: the entire original side pattern is checked by an explicit
source-reading loop, with one polynomial-cost iteration per error slot. -/
theorem patternLoop_run (C : Ctx) (c : Call) (suffix : List Bool)
    (a : DS VV) (hc : Cst a) (P : Prop) [Decidable P]
    (cut b offset code count : ℕ) (hb : 1≤b)
    (hflag : a.env patternFlag=bnat P) (hcut : a.env heavyThreshold=cut)
    (hB : a.env patternBlockSize=b) (hR : a.env patternRadix=b+1)
    (hstart : a.env patternBlock=offset) (hend : a.env patternEnd=offset+count)
    (hcode : a.env patternCode=code) (hsource : b*(offset+count)≤c.n)
    (hcw : C.cw=callWord c++suffix) (hW : 2*C.cw.length+8≤C.Wd)
    (hL : 2*C.cw.length+4<2^C.Wd) (hn : c.n<2^C.Wd)
    (hradix : 2*(b+1)≤2^C.Wd) (hendfit : offset+count<2^C.Wd) :
    Hs C patternLoop a (count*(1204*(C.cw.length+2)^3+2)+2) (fun z =>
      z.env patternCode=code/(b+1)^count ∧ z.env patternBlock=offset+count ∧
      z.env patternFlag=bnat (P ∧ prefixNonheavy c cut b offset code count) ∧
      z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z patternStepScratch) := by
  let I : ℕ→DS VV→Prop := fun j z =>
    z.env patternCode=code/(b+1)^j ∧ z.env patternBlock=offset+j ∧
    z.env patternFlag=bnat (P ∧ prefixNonheavy c cut b offset code j) ∧
    z.env patternRadix=b+1 ∧ z.env patternBlockSize=b ∧
    z.env heavyThreshold=cut ∧ z.env patternEnd=offset+count ∧
    z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z patternStepScratch
  have step : ∀j<count,∀z,I j z→
      Cnd.eval z (.lt patternBlock patternEnd)=true ∧
      Hs C patternStep z (1204*(C.cw.length+2)^3) (I (j+1)) := by
    intro j hj z ⟨zc,zb,zf,zR,zB,zcut,ze,zw,zo,zconst,zfr⟩
    have valid : z.env patternCode%z.env patternRadix≠0 →
        z.env patternBlock*z.env patternBlockSize+(z.env patternCode%z.env patternRadix-1)<c.n := by
      intro hd
      have hm : z.env patternCode%z.env patternRadix<b+1 := by
        rw [zR]
        exact Nat.mod_lt _ (by omega)
      have hbnd : b*(offset+j+1)≤c.n :=
        (Nat.mul_le_mul_left b (show offset+j+1≤offset+count by omega)).trans hsource
      have hrem : z.env patternCode%z.env patternRadix-1<b := by omega
      rw [zb,zB]
      nlinarith only [hbnd,hrem]
    refine ⟨by simp [Cnd.eval,zb,ze]; omega,?_⟩
    refine (patternStep_run C c suffix z zconst (P ∧ prefixNonheavy c cut b offset code j)
      zf (by rw [zR]; omega) (by rw [zR]; exact hradix) valid hcw hW hL hn
      (by rw [zb]; omega)).mono le_rfl ?_
    rintro d ⟨dc,db,df,dw,doo,dconst,dfr⟩
    refine ⟨?_,by simpa only [zb,Nat.add_assoc] using db,?_,
      (dfr _ (by decide)).trans zR,(dfr _ (by decide)).trans zB,
      (dfr _ (by decide)).trans zcut,(dfr _ (by decide)).trans ze,
      dw.trans zw,doo.trans zo,dconst,zfr.trans dfr⟩
    · rw [dc,zc,zR,Nat.div_div_eq_div_mul,←pow_succ]
    · simpa [bnat,zcut,zB,zb,zc,zR,prefixNonheavy,and_assoc] using df
  have stop : ∀z,I count z→Cnd.eval z (.lt patternBlock patternEnd)=false := by
    rintro z ⟨_,zb,_,_,_,_,ze,_⟩
    simp [Cnd.eval,zb,ze]
  have start : I 0 a := by
    exact ⟨by simpa using hcode,by simpa using hstart,
      by simpa only [prefixNonheavy,and_true] using hflag,
      hR,hB,hcut,hend,rfl,rfl,hc,Fr.refl _ _⟩
  refine (Hs.loopN (C := C) (c := .lt patternBlock patternEnd) (s := patternStep)
    (show patternBlock≠patternEnd by decide) I count (1204*(C.cw.length+2)^3)
    step stop a start).mono le_rfl ?_
  rintro z ⟨zc,zb,zf,_,_,_,_,zw,zo,zconst,zfr⟩
  exact ⟨zc,zb,zf,zw,zo,zconst,zfr⟩

end NearQuarticWires.StageCert.Incidence
