import Proof.Quartic.StageCert.MaskParameters
import Proof.Quartic.StageCert.MomentRow

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells
open NearQuarticWires.StageLift

/-- `sec:walks`, `sec:params` and `lem:print`, paper/paper.tex: reload original chain
length, final scales and sign ordinal after mask scratch is finished. -/
def loadLinearParameters : St VV MM :=
  .seq (StageMain.readParameter ⟨40,by decide⟩ chainRows)
    (.seq (StageMain.readParameter ⟨39,by decide⟩ finalScale)
      (.seq (StageMain.readParameter ⟨41,by decide⟩ finalOffset)
        (.seq (.op (.copy newtonTau sourceSignOrdinal)) selectMomentRow)))

/-- `lem:print` and `prop:time`, paper/paper.tex: original linear-form metadata is obtained by actual
retained-scalar reads and physical copies. Digits keep their requested
row; final error uses the exact original last-chain row and A offset. -/
theorem loadLinearParameters_run (C : Ctx) (p : Cells.Parameters)
    (a : DS VV MM) (hc : Cst a) (hram : a.ram parameterStore=parameterScalars p)
    (hW : 6≤C.Wd) (hpos : 1≤p.J) :
    Hs C loadLinearParameters a (a.rc parameterStore+1000) (fun z=>
      z.env chainRows=p.J ∧ z.env finalScale=p.M1 ∧ z.env finalOffset=p.A ∧
      z.env newtonTau=a.env sourceSignOrdinal ∧
      z.env requestedChainRow=(if a.env sourceTestTag=1 then a.env requestedChainRow else p.J-1) ∧
      z.rc parameterStore=42 ∧ StageMain.parameterRest z=StageMain.parameterRest a ∧
      Cst z ∧ Fr a z [t2,vJ,c0,chainRows,finalScale,finalOffset,newtonTau,requestedChainRow]) := by
  have h64 : 64≤2^C.Wd := by
    have hh := Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide) hW
    norm_num at hh
    exact hh
  have hJ : (parameterScalars p).getD 40 0=p.J := rfl
  have hM : (parameterScalars p).getD 39 0=p.M1 := rfl
  have hA : (parameterScalars p).getD 41 0=p.A := rfl
  unfold loadLinearParameters
  apply Hx.hs
  refine Hs.then (StageMain.readParameter_run C p ⟨40,by decide⟩ chainRows
    a hc hram (by change 40<2^C.Wd; omega) (by decide))
    (fun b ⟨bj,br,bs,bc,bfr⟩ n1 hn1=>?_)
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
  refine Hs.then (StageMain.readParameter_run C p ⟨39,by decide⟩ finalScale
    b bc (by rw [bram]; exact hram) (by change 39<2^C.Wd; omega) (by decide))
    (fun d ⟨dm,dr,ds,dc,dfr⟩ n2 hn2=>?_)
  have dram : d.ram=a.ram := (congrArg (fun q=>q.2.2.1) ds).trans bram
  refine Hs.then (StageMain.readParameter_run C p ⟨41,by decide⟩ finalOffset
    d dc (by rw [dram]; exact hram) (by change 41<2^C.Wd; omega) (by decide))
    (fun e ⟨ea,er,es,ec,efr⟩ n3 hn3=>?_)
  refine Hs.then (hs_copy C newtonTau sourceSignOrdinal e (by decide))
    (fun f hf n4 hn4=>?_)
  subst hf
  let f := e.set newtonTau (e.env sourceSignOrdinal)
  have ef : Fr a e [t2,vJ,c0,chainRows,finalScale,finalOffset] :=
    (bfr.weaken (by decide)).trans ((dfr.weaken (by decide)).trans (efr.weaken (by decide)))
  have ff : Fr a f [t2,vJ,c0,chainRows,finalScale,finalOffset,newtonTau] :=
    (ef.weaken (by decide)).trans (Fr.set _ _ (by simp))
  have fc : Cst f := Cst.of_fr (T := [newtonTau]) ec (Fr.set _ _ (by simp)) (by decide)
  have fj : f.env chainRows=p.J := by
    change e.env chainRows=p.J
    exact (efr _ (by decide)).trans ((dfr _ (by decide)).trans (bj.trans hJ))
  refine Hs.last (selectMomentRow_run C (a.env sourceTestTag) (a.env requestedChainRow)
    p.J f fc (ff _ (by decide)) (ff _ (by decide)) fj hpos)
    (fun z ⟨zrow,zs,zc,zfr⟩ n5 hn5=>?_)
  have zsame := Same.of_sh zs
  have zrest : StageMain.parameterRest z=StageMain.parameterRest f := by
    simp only [StageMain.parameterRest,zsame.ip,zsame.out,zsame.ram,zsame.rc,
      zsame.kin,zsame.kout,zsame.kc]
  refine ⟨⟨(zfr _ (by decide)).trans fj,?_,?_,?_,zrow,?_,
    zrest.trans (es.trans (ds.trans bs)),zc,
    (ff.weaken (by decide)).trans (zfr.weaken (by decide))⟩,?_⟩
  · rw [zfr _ (by decide)]
    change e.env finalScale=p.M1
    exact (efr _ (by decide)).trans (dm.trans hM)
  · rw [zfr _ (by decide)]
    change e.env finalOffset=p.A
    exact ea.trans hA
  · rw [zfr _ (by decide)]
    change e.env sourceSignOrdinal=a.env sourceSignOrdinal
    exact ef _ (by decide)
  · rw [zsame.rc]
    exact er
  · rw [br] at hn2
    rw [dr] at hn3
    change n1≤a.rc parameterStore+7*40+13 at hn1
    change n2≤41+7*39+13 at hn2
    change n3≤40+7*41+13 at hn3
    omega

end NearQuarticWires.StageCert.Tokens
