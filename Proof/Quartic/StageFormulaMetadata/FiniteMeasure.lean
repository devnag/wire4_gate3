import Proof.Gates.Cells.Run
import Proof.Gates.Cells.Arith

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Cells NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ} (cap : ℕ)

/-- `lem:print`, paper/paper.tex: count the
actual bits of one finite input frame and physically rewind it. -/
def measureFrame (input : Fin (ns+1)) (count scratch : Fin nr) : WMX ns nr :=
  .seq (.whs input (.seq (WMX.inc count) (.seq (WMX.fwd input) (WMX.fwd input))))
    (repK count scratch (.seq (WMX.bwd input) (WMX.bwd input)))

/-- `prop:time`, paper/paper.tex: the workspace
initializer obtains the source length by a paid finite scan, without
an externally supplied count or a leading-size-field assumption. -/
theorem measureFrame_spec (input : Fin (ns+1)) {count scratch : Fin nr}
    (hne : count ≠ scratch) (a : WState ns nr) (bits : List Bool)
    (hin : a.st input = frame bits) (hip : a.sh input = 0)
    (hc : a.val count = 0) (hs : a.val scratch = 0)
    (hcap : 2*bits.length+4 ≤ cap) :
    WXExec cap (measureFrame input count scratch) a
      (a.setv count bits.length) (30*bits.length+10) := by
  let len := bits.length
  have scan : ∀ remaining index, index+remaining=len → ∀ b : WState ns nr,
      b=(a.seth input (2*index)).setv count index →
      WXExec cap (.whs input (.seq (WMX.inc count)
        (.seq (WMX.fwd input) (WMX.fwd input)))) b
        ((a.seth input (2*len)).setv count len) (remaining*10+1) := by
    intro remaining
    induction remaining with
    | zero =>
        intro index hindex b hb
        have hindex' : index=len := by omega
        subst index
        subst b
        apply WXExec.whsF
        show readTapeBit _ _ = false
        simp only [WState.setv_st,WState.seth_st,WState.setv_sh,
          WState.seth_sh,Function.update_self,hin]
        change (frame bits).getD (2*len) false=false
        rw [frame_getD_even]
        simp [len]
    | succ remaining ih =>
        intro index hindex b hb
        subst b
        have hbit : wbit ((a.seth input (2*index)).setv count index) input=true := by
          show readTapeBit _ _=true
          simp only [WState.setv_st,WState.seth_st,WState.setv_sh,
            WState.seth_sh,Function.update_self,hin]
          change (frame bits).getD (2*index) false=true
          rw [frame_getD_even]
          simp only [decide_eq_true_eq]
          omega
        have e1 := WXExec.inc cap count ((a.seth input (2*index)).setv count index)
          (by simp; dsimp [len] at hindex; omega)
        simp only [WState.setv_val,Function.update_self] at e1
        let b1 := ((a.seth input (2*index)).setv count index).setv count (index+1)
        have e2 := WXExec.fwd cap input b1
        have e3 := WXExec.fwd cap input (b1.seth input (b1.sh input+1))
        have heq : (b1.seth input (b1.sh input+1)).seth input
            ((b1.seth input (b1.sh input+1)).sh input+1)=
            (a.seth input (2*(index+1))).setv count (index+1) := by
          apply WState.eq
          · funext stream
            by_cases hstream : stream=input
            · subst stream; simp [b1]; ring
            · simp [b1,Function.update_of_ne hstream]
          · rfl
          · funext reg
            by_cases hreg : reg=count
            · subst reg; simp [b1]
            · simp [b1,Function.update_of_ne hreg]
          · rfl
        rw [heq] at e3
        have erest := ih (index+1) (by omega) _ rfl
        refine (WXExec.whsT hbit (WXExec.seq e1 (WXExec.seq e2 e3)) erest).mono ?_
        omega
  have estart : (a.seth input (2*0)).setv count 0=a := by
    apply WState.eq
    · funext stream
      by_cases hstream : stream=input
      · subst stream; simp [hip]
      · simp [Function.update_of_ne hstream]
    · rfl
    · funext reg
      by_cases hreg : reg=count
      · subst reg; simp [hc]
      · simp [Function.update_of_ne hreg]
    · rfl
  have e1 := scan len 0 (by omega) a estart.symm
  let state : ℕ→WState ns nr := fun index =>
    (a.seth input (2*len-2*index)).setv count len
  have e2 := Runs.repE (cap:=cap) (K:=count) (K2:=scratch)
    (body:=.seq (WMX.bwd input) (WMX.bwd input)) hne 3 len state
    (by dsimp [len]; omega) (fun index=>by simp [state])
    (fun index=>by simp [state,Function.update_of_ne hne.symm])
    (by
      intro index hindex first second
      let b := ((state index).setv count first).setv scratch second
      have eb1 := WXExec.bwd cap input b
      have eb2 := WXExec.bwd cap input (b.seth input (b.sh input-1))
      refine (WXExec.seq eb1 eb2).cast cap ?_ (by omega)
      apply WState.eq
      · funext stream
        by_cases hstream : stream=input
        · subst stream; simp [b,state]; omega
        · simp [b,state,Function.update_of_ne hstream]
      · rfl
      · rfl
      · rfl)
    (by simp [state]) (by simp [state,Function.update_of_ne hne.symm,hs])
  have hzero : state 0=(a.seth input (2*len)).setv count len := by simp [state]
  have hlast : state len=a.setv count len := by
    apply WState.eq
    · funext stream
      by_cases hstream : stream=input
      · subst stream; simp [state,hip]
      · simp [state,Function.update_of_ne hstream]
    · rfl
    · rfl
    · rfl
  rw [hzero,hlast] at e2
  exact (WXExec.seq e1 e2).mono (by omega)

end NearQuarticWires.StageFormulaMetadata
