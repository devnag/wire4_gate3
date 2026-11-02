import Proof.Quartic.StageCert.SourceMetadata
import Proof.Quartic.StageMain.ParameterGet

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells
open NearQuarticWires.StageLift

/-- `def:mask`, `sec:params` and `lem:print`, paper/paper.tex: load the literal selected
cutoff, degree limit and witness-selection offset from the actual
retained parameter records. -/
def loadMaskParameters : St VV MM :=
  .seq (StageMain.readParameter ⟨10,by decide⟩ newtonTau)
    (.seq (StageMain.readParameter ⟨12,by decide⟩ maskLimit)
      (.seq (.op (.inc maskLimit)) (StageMain.readParameter ⟨6,by decide⟩ selectionStart)))

/-- `lem:print` and `prop:time`, paper/paper.tex: all mask fields are produced by paid scalar-store
reads and the exact limit increment. The original source and all
whole-test metadata remain unchanged. -/
theorem loadMaskParameters_run (C : Ctx) (p : Cells.Parameters)
    (a : DS VV MM) (hc : Cst a) (hram : a.ram parameterStore=parameterScalars p)
    (hW : 5≤C.Wd) (hX : p.Xmax+1<2^C.Wd) :
    Hs C loadMaskParameters a (a.rc parameterStore+270) (fun z=>
      z.env newtonTau=p.tau ∧ z.env maskLimit=p.Xmax+1 ∧ z.env selectionStart=p.k ∧
      z.rc parameterStore=7 ∧ StageMain.parameterRest z=StageMain.parameterRest a ∧
      Cst z ∧ Fr a z [t2,vJ,c0,newtonTau,maskLimit,selectionStart]) := by
  have h32 : 32≤2^C.Wd := by
    have hh := Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide) hW
    norm_num at hh
    exact hh
  have htau : (parameterScalars p).getD 10 0=p.tau := rfl
  have hXmax : (parameterScalars p).getD 12 0=p.Xmax := rfl
  have hk : (parameterScalars p).getD 6 0=p.k := rfl
  unfold loadMaskParameters
  apply Hx.hs
  refine Hs.then (StageMain.readParameter_run C p ⟨10,by decide⟩ newtonTau
    a hc hram (by change 10<2^C.Wd; omega) (by decide))
    (fun b ⟨bt,br,bs,bc,bfr⟩ n1 hn1=>?_)
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
  refine Hs.then (StageMain.readParameter_run C p ⟨12,by decide⟩ maskLimit
    b bc (by rw [bram]; exact hram) (by change 12<2^C.Wd; omega) (by decide))
    (fun d ⟨dx,dr,ds,dc,dfr⟩ n2 hn2=>?_)
  have dx' : d.env maskLimit=p.Xmax := dx.trans hXmax
  refine Hs.then (hs_inc C maskLimit d (by rw [dx']; exact hX))
    (fun e he n3 hn3=>?_)
  subst he
  let e := d.set maskLimit (d.env maskLimit+1)
  have ec : Cst e := Cst.of_fr (T := [maskLimit]) dc (Fr.set _ _ (by simp)) (by decide)
  have eram : e.ram=a.ram := (congrArg (fun q=>q.2.2.1) ds).trans bram
  refine Hs.last (StageMain.readParameter_run C p ⟨6,by decide⟩ selectionStart
    e ec (by rw [eram]; exact hram) (by change 6<2^C.Wd; omega) (by decide))
    (fun z ⟨zk,zr,zs,zc,zfr⟩ n4 hn4=>?_)
  have erest : StageMain.parameterRest e=StageMain.parameterRest d := rfl
  refine ⟨⟨?_,?_,zk.trans hk,zr,zs.trans (erest.trans (ds.trans bs)),zc,
    (bfr.weaken (by decide)).trans ((dfr.weaken (by decide)).trans
      ((Fr.set _ _ (by decide)).trans (zfr.weaken (by decide))))⟩,?_⟩
  · rw [zfr _ (by decide)]
    change d.env newtonTau=p.tau
    exact (dfr _ (by decide)).trans (bt.trans htau)
  · rw [zfr _ (by decide)]
    change d.env maskLimit+1=p.Xmax+1
    rw [dx']
  · rw [br] at hn2
    change n1≤a.rc parameterStore+7*10+13 at hn1
    change n2≤11+7*12+13 at hn2
    change n4≤d.rc parameterStore+7*6+13 at hn4
    rw [dr] at hn4
    change n4≤13+7*6+13 at hn4
    omega

end NearQuarticWires.StageCert.Tokens
