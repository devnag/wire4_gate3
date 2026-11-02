import Proof.Quartic.StageCert.SelectedGate

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain

/-- `def:mask` and the witness of `sec:algorithm`, paper/paper.tex: the selected bit is fetched from its actual source
frame before rereading the original raw gate at all four points. -/
def selectedSourceGate : St VV := .seq (.op (.copy cornerGateStart vPOS))
  (.seq sourceWitnessBit (.seq (seekW cornerGateStart) selectedGate))

/-- `def:mask`, paper/paper.tex: a complete selected
occurrence scan combines witness addressing and raw-gate evaluation scratch. -/
def selectedSourceScratch : List (Fin VV) :=
  sourceWitnessScratch++selectedGateScratch

/-- `def:mask`, the witness of `sec:algorithm` and `prop:time`,
paper/paper.tex: one selected
population contribution is computed from literal source bytes, without
supplied witness bits, gate values or residual magnitudes. -/
theorem selectedSourceGate_run (C : Ctx) {n : ℕ} (g : NormalizedThresholdGate n)
    (a : DS VV) (hc : Cst a) (rest pre bits suffix : List Bool) (index : ℕ)
    (hin : C.cw.drop a.cp=gateWord g++rest) (hbase : a.cp≤C.cw.length)
    (hW : C.cw.length+3≤C.Wd) (hpoint : ∀l,a.env (cornerPoint l)<2^C.Wd)
    (hi : index<bits.length) (hWitnessBase : a.env sourceWitnessBase=pre.length)
    (hindex : a.env sourceWitnessIndex=index)
    (hcw : C.cw=pre++frame bits++suffix) (hfit : a.env populationTotal+2<2^C.Wd) :
    Hs C selectedSourceGate a (900*(C.cw.length+2)^2+100) (fun z =>
      z.env populationTotal=a.env populationTotal+
        (if Algorithm.witnessBit bits index then
          (fourBitDifference (fun l=>g.eval (packedPoint n (a.env (cornerPoint l))))).natAbs
        else 0) ∧
      z.cp=a.cp+(gateWord g).length ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧
      FrS a z selectedSourceScratch) := by
  have hL : C.cw.length<2^C.Wd := by
    have h := Nat.lt_two_pow_self (n := C.Wd)
    omega
  unfold selectedSourceGate
  apply Hx.hs
  refine Hs.then (hs_copy C cornerGateStart vPOS a (by decide))
    (fun r hr n0 hn0 => ?_)
  subst hr
  let r := a.set cornerGateStart (a.env vPOS)
  have rf : Fr a r [cornerGateStart] := Fr.set _ _ (by simp)
  have rc : Cst r := Cst.of_fr hc rf (by decide)
    (by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos)
  refine Hs.then (sourceWitnessBit_run C r rc pre bits suffix index hi
    ((rf _ (by decide)).trans hWitnessBase) ((rf _ (by decide)).trans hindex) hcw hL)
    (fun b ⟨bs,_bc,bw,bo,bconst,bfr⟩ n1 hn1 => ?_)
  have bb : b.env cornerGateStart=a.cp := by rw [bfr _ (by decide)]; simp [r,hc.pos]
  refine Hs.then (seekW_spec cornerGateStart (by decide) (by decide) b bconst
    a.cp bb hbase hL)
    (fun e ⟨ec,ew,eo,econst,efr⟩ n2 hn2 => ?_)
  have ef : Fr a e (sourceWitnessScratch++[cornerGateStart]) :=
    (rf.weaken (by simp)).trans
      ((bfr.weaken (by intro y hy; exact List.mem_append_left _ hy)).trans (efr.weaken (by decide)))
  have ep : ∀l,e.env (cornerPoint l)=a.env (cornerPoint l) := by
    intro l
    exact ef _ (by fin_cases l <;> decide)
  have et : e.env populationTotal=a.env populationTotal := ef _ (by decide)
  have es : e.env sourceWitnessResult=(Algorithm.witnessBit bits index).toNat :=
    (efr _ (by decide)).trans bs
  refine Hs.last (selectedGate_run C g e econst rest (by rw [ec]; exact hin)
    (by rw [ec]; exact hbase) hW (by intro l; rw [ep]; exact hpoint l)
    (Algorithm.witnessBit bits index) es (by rw [et]; exact hfit))
    (fun z ⟨zt,zc,zw,zo,zconst,zfr⟩ n3 hn3 => ?_)
  have fEq : (fun l=>g.eval (packedPoint n (e.env (cornerPoint l))))=
      (fun l=>g.eval (packedPoint n (a.env (cornerPoint l)))) := by
    funext l
    rw [ep]
  refine ⟨⟨by simpa only [et,fEq] using zt,by rw [zc,ec],
    zw.trans (ew.trans bw),zo.trans (eo.trans bo),zconst,?_⟩,?_⟩
  · exact (ef.toS.weaken (by decide)).trans (zfr.weaken (by decide))
  · have hp : C.cw.length+2≤(C.cw.length+2)^2 := Nat.le_self_pow (by decide) _
    nlinarith only [hn0,hn1,hn2,hn3,hbase,hp]

end NearQuarticWires.StageCert
