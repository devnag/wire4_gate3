import Proof.Quartic.StageCert.PopulationStep

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain

/-- `def:mask`, paper/paper.tex: all original occurrence
positions are traversed exactly once by the selected-population source loop. -/
def populationLoop : St VV := .loop (.lt populationIndex populationLimit) populationStep

/-- `def:mask`, the witness of `sec:algorithm` and `prop:time`,
paper/paper.tex: the complete
selected population is computed from literal raw-gate and witness source
words, with an exact linear occurrence census and polynomial bit overhead. -/
theorem populationLoop_run (C : Ctx) {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (a : DS VV) (hc : Cst a) (rest pre bits suffix : List Bool) (index : ℕ)
    (hin : C.cw.drop a.cp=gs.flatMap gateWord++rest) (hbase : a.cp≤C.cw.length)
    (hW : C.cw.length+3≤C.Wd) (hpoint : ∀l,a.env (cornerPoint l)<2^C.Wd)
    (hbits : index+gs.length≤bits.length) (hWitnessBase : a.env sourceWitnessBase=pre.length)
    (hindex : a.env sourceWitnessIndex=index) (hzero : a.env populationIndex=0)
    (hlimit : a.env populationLimit=gs.length)
    (hcw : C.cw=pre++frame bits++suffix)
    (hfit : a.env populationTotal+2*gs.length<2^C.Wd) (hG : gs.length<2^C.Wd) :
    Hs C populationLoop a (gs.length*(900*(C.cw.length+2)^2+106)+2) (fun z =>
      z.env populationTotal=a.env populationTotal+
        populationPrefix gs (fun l=>a.env (cornerPoint l)) bits index gs.length ∧
      z.env sourceWitnessIndex=index+gs.length ∧ z.env populationIndex=gs.length ∧
      C.cw.drop z.cp=rest ∧ z.cp≤C.cw.length ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧
      FrS a z populationScratch) := by
  let points := fun l=>a.env (cornerPoint l)
  let I : ℕ→DS VV→Prop := fun j b =>
    b.env populationTotal=a.env populationTotal+populationPrefix gs points bits index j ∧
    b.env sourceWitnessIndex=index+j ∧ b.env populationIndex=j ∧ b.env populationLimit=gs.length ∧
    C.cw.drop b.cp=(gs.drop j).flatMap gateWord++rest ∧ b.cp≤C.cw.length ∧
    b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ FrS a b populationScratch
  have hBitsFit : bits.length<2^C.Wd := by
    have he := congrArg List.length hcw
    simp only [List.length_append,NearCubicGates.Close.Dispatch.frame_length] at he
    have hh := Nat.lt_two_pow_self (n := C.Wd)
    omega
  have step : ∀j<gs.length,∀b,I j b→
      Cnd.eval b (.lt populationIndex populationLimit)=true ∧
      Hs C populationStep b (900*(C.cw.length+2)^2+104) (I (j+1)) := by
    intro j hj b ⟨bt,bi,bj,bl,bword,bcp,bw,bo,bconst,bfr⟩
    have hword : C.cw.drop b.cp=gateWord gs[j]++((gs.drop (j+1)).flatMap gateWord++rest) := by
      rw [bword,List.drop_eq_getElem_cons hj,List.flatMap_cons,List.append_assoc]
    have bp : ∀l,b.env (cornerPoint l)=points l := by
      intro l
      exact bfr _ (by fin_cases l <;> decide) (by fin_cases l <;> decide)
    have bBase : b.env sourceWitnessBase=pre.length :=
      (bfr _ (by decide) (by decide)).trans hWitnessBase
    have bfit : b.env populationTotal+2<2^C.Wd := by
      rw [bt]
      have hp := populationPrefix_le gs points bits index j
      omega
    refine ⟨by simp [Cnd.eval,bj,bl,hj],?_⟩
    refine (populationStep_run C gs[j] b bconst _ pre bits suffix (index+j)
      hword bcp hW (by intro l; rw [bp]; exact hpoint l)
      (by omega) bBase bi hcw bfit (by omega) (by rw [bj]; omega)).mono le_rfl ?_
    rintro d ⟨dt,di,dj,dc,dw,doo,dconst,dfr⟩
    have dword : C.cw.drop d.cp=(gs.drop (j+1)).flatMap gateWord++rest := by
      rw [dc,←List.drop_drop,hword,List.drop_left]
    have hlen := congrArg List.length hword
    simp only [List.length_drop,List.length_append] at hlen
    refine ⟨?_,by simpa only [Nat.add_assoc] using di,by simpa only [bj] using dj,
      (dfr _ (by decide) (by decide)).trans bl,dword,by rw [dc]; omega,
      dw.trans bw,doo.trans bo,dconst,bfr.trans dfr⟩
    · have pEq : (fun l=>b.env (cornerPoint l))=points := funext bp
      rw [dt,pEq,bt,populationPrefix_succ,dif_pos hj,Nat.add_assoc]
  have stop : ∀b,I gs.length b→Cnd.eval b (.lt populationIndex populationLimit)=false := by
    rintro b ⟨_,_,bj,bl,_⟩
    simp [Cnd.eval,bj,bl]
  have start : I 0 a := by
    exact ⟨by simp [populationPrefix],by simpa using hindex,hzero,hlimit,
      by simpa using hin,hbase,rfl,rfl,hc,fun _ _ _=>rfl⟩
  refine (Hs.loopN (C := C) (c := .lt populationIndex populationLimit) (s := populationStep)
    (show populationIndex≠populationLimit by decide) I gs.length
    (900*(C.cw.length+2)^2+104) step stop a start).mono le_rfl ?_
  rintro z ⟨zt,zi,zj,_,zword,zc,zw,zo,zconst,zfr⟩
  exact ⟨zt,zi,zj,by simpa using zword,zc,zw,zo,zconst,zfr⟩

end NearQuarticWires.StageCert
