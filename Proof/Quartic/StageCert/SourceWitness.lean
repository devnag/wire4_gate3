import Proof.Quartic.StageCert.WitnessAddress
import Proof.Quartic.Program.Prefix

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Dispatch

/-- The witness of `sec:algorithm`, paper/paper.tex:
one retained framed bit is read from the actual source by its paid address. -/
def sourceWitnessBit : St VV := .seq witnessAddress
  (.seq (seekW sourceWitnessTarget) (.seq rdc (.op (.copy sourceWitnessResult t0))))

/-- The witness of `sec:algorithm`, paper/paper.tex:
the framed source read changes only its address, bit result and source cursor. -/
def sourceWitnessScratch : List (Fin VV) := [sourceWitnessTarget,sourceWitnessResult,t0,vPOS,vJ]

/-- The witness of `sec:algorithm` and `prop:time`, paper/paper.tex: retained witness bits are physically read
from their literal framed source, not supplied as a decoded bit oracle. -/
theorem sourceWitnessBit_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (pre bits suffix : List Bool) (index : ℕ) (hi : index<bits.length)
    (hbase : a.env sourceWitnessBase=pre.length)
    (hindex : a.env sourceWitnessIndex=index)
    (hcw : C.cw=pre++frame bits++suffix) (hfit : C.cw.length<2^C.Wd) :
    Hs C sourceWitnessBit a (5*C.cw.length+30) (fun z =>
      z.env sourceWitnessResult=(Algorithm.witnessBit bits index).toNat ∧
      z.cp=pre.length+2*index+2 ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧
      Fr a z sourceWitnessScratch) := by
  let target := pre.length+2*index+1
  have ht : target<C.cw.length := by
    rw [hcw,List.length_append,List.length_append,NearCubicGates.Close.Dispatch.frame_length]
    dsimp [target]
    omega
  have hj : 2*index+1<(frame bits).length := by rw [NearCubicGates.Close.Dispatch.frame_length]; omega
  have hd : C.cw.drop pre.length=frame bits++suffix := by
    rw [hcw]
    simp only [List.append_assoc,List.drop_left]
  have hbit : bitOf C.cw target=(Algorithm.witnessBit bits index).toNat := by
    have h := bitOf_drop hd (2*index+1) hj
    rw [NearCubicGates.Close.Dispatch.frame_odd] at h
    exact h
  unfold sourceWitnessBit
  apply Hx.hs
  refine Hs.then (witnessAddress_run C a hc (by rw [hbase,hindex]; exact ht.trans hfit))
    (fun r ⟨rt,_rc,rw,ro,rconst,rf⟩ n1 hn1 => ?_)
  have rtarget : r.env sourceWitnessTarget=target := by simpa only [hbase,hindex] using rt
  refine Hs.then (seekW_spec sourceWitnessTarget (by decide) (by decide) r rconst
    target rtarget ht.le hfit)
    (fun b ⟨bc,bw,bo,bconst,bfr⟩ n2 hn2 => ?_)
  refine Hs.then (rdc_spec b bconst.pos (by rw [bc]; exact ht) hfit)
    (fun d ⟨db,dp,dc,dw,doo,dfr⟩ n3 hn3 => ?_)
  have dconst : Cst d := Cst.of_fr bconst dfr (by decide) (dp.trans dc.symm)
  refine Hs.last (hs_copy C sourceWitnessResult t0 d (by decide))
    (fun z hz n4 hn4 => ?_)
  subst hz
  refine ⟨⟨?_,?_,dw.trans (bw.trans rw),doo.trans (bo.trans ro),?_,?_⟩,?_⟩
  · rw [DS.set_env_self,db,bc,hbit]
  · change d.cp=_
    rw [dc,bc]
  · exact Cst.of_fr dconst (Fr.set (T := [sourceWitnessResult]) _ _ (by simp)) (by decide)
      (by rw [DS.set_env_ne _ _ (by decide)]; exact dconst.pos)
  · exact (rf.weaken (by decide)).trans ((bfr.weaken (by decide)).trans
      ((dfr.weaken (by decide)).trans (Fr.set _ _ (by simp [sourceWitnessScratch]))))
  · omega

end NearQuarticWires.StageCert
