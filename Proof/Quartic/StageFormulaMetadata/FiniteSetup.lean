import Proof.Quartic.StageFormulaMetadata.FiniteMeasure

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Cells NearCubicGates.Close.WordPrograms

variable {ns nr V M : ℕ}

/-- `prop:time`, paper/paper.tex: initialize
a linear binary workspace using only the physically counted length. -/
theorem scaleCount_spec (cap : ℕ) {count scratch target : Fin nr}
    (hct : count ≠ target) (hcs : count ≠ scratch) (hst : scratch ≠ target)
    (factor len : ℕ) (a : WState ns nr) (hc : a.val count=len)
    (hs : a.val scratch=0) (ht : a.val target=0)
    (hcap : 2*len+factor*len ≤ cap) :
    WXExec cap (repK count scratch (incN target factor)) a
      (a.setv target (factor*len)) (len*(4*factor+8)+7*len+3) := by
  let state : ℕ→WState ns nr := fun index=>a.setv target (factor*index)
  have erun := Runs.repE (cap:=cap) (K:=count) (K2:=scratch)
    (body:=incN target factor) hcs (4*factor) len state (by omega)
    (fun index=>by simp [state,Function.update_of_ne hct,hc])
    (fun index=>by simp [state,Function.update_of_ne hst,hs])
    (by
      intro index hindex first second
      let b := ((state index).setv count first).setv scratch second
      have hvalue : b.val target=factor*index := by
        simp [b,state,Function.update_of_ne hct.symm,Function.update_of_ne hst.symm]
      have hbound : b.val target+factor ≤ cap := by
        rw [hvalue,←Nat.mul_succ]
        have hmul := Nat.mul_le_mul_left factor hindex
        omega
      refine (incN_spec cap target factor b hbound).cast cap ?_ le_rfl
      apply WState.eq
      · rfl
      · rfl
      · funext reg
        by_cases ht' : reg=target
        · subst reg
          simp [b,state,Function.update_of_ne hct.symm,Function.update_of_ne hst.symm]
          ring
        · simp only [b,state,WState.setv_val,Function.update_apply]
          split_ifs <;> simp_all
      · rfl)
    (by simp [state,Function.update_of_ne hct,hc])
    (by simp [state,Function.update_of_ne hst,hs])
  have hstart : state 0=a := by simp [state,BinW.setv_same ht]
  rw [hstart] at erun
  exact erun

/-- `prop:time`, paper/paper.tex: the formatter's
binary registers have width linear in the complete finite packet. -/
def finiteWidth (len : ℕ) : ℕ := 100*(len+1)

/-- `prop:time`, paper/paper.tex: measure the
whole packet, compute its workspace width, and initialize the ruler. -/
def finiteSetupA (K : Callee) : WMX (NS M (TSK K) V) (NR M) :=
  .seq (measureFrame sIN rG rC2)
    (.seq (repK rG rC2 (incN rK 100))
      (.seq (incN rK 100) (incN rR 3)))

/-- `prop:time`, paper/paper.tex: all source
measurement and size-register writes are charged before cell setup. -/
def finiteSetupACost (len : ℕ) : ℕ :=
  (30*len+10)+(len*(4*100+8)+7*len+3)+400+12+3

/-- `prop:time`, paper/paper.tex: the actual
finite-source initializer establishes the standard cell setup state,
with empty callee reserves and no supplied size field. -/
theorem finiteSetupA_spec (K : Callee) (bits : List Bool) (cap : ℕ)
    (hcap : 2*bits.length+4*finiteWidth bits.length+20 ≤ cap) :
    WXExec cap (finiteSetupA (V:=V) (M:=M) K)
      (NearCubicGates.Close.Interfaces.startState (NS M (TSK K) V) (NR M) bits)
      (stA (t:=TSK K) bits.length (finiteWidth bits.length) 0 0 bits)
      (finiteSetupACost bits.length) := by
  let a := NearCubicGates.Close.Interfaces.startState (NS M (TSK K) V) (NR M) bits
  have hz : ∀ reg, a.val reg=0 := fun _=>rfl
  have hCG : (rC2 : Fin (NR M))≠rG := by lay_ne
  have hKG : (rK : Fin (NR M))≠rG := by lay_ne
  have hRK : (rR : Fin (NR M))≠rK := by lay_ne
  have hRG : (rR : Fin (NR M))≠rG := by lay_ne
  have e1 := measureFrame_spec cap sIN (count:=rG) (scratch:=rC2) (by lay_ne)
    a bits rfl rfl rfl rfl (by omega)
  let b := a.setv rG bits.length
  have e2 := scaleCount_spec cap (count:=rG) (scratch:=rC2) (target:=rK)
    (by lay_ne) (by lay_ne) (by lay_ne) 100 bits.length b (by simp [b])
    (by simp only [b,WState.setv_val,Function.update_of_ne hCG,hz])
    (by simp only [b,WState.setv_val,Function.update_of_ne hKG,hz]) (by
      unfold finiteWidth at hcap
      omega)
  let d := b.setv rK (100*bits.length)
  have e3 := incN_spec cap rK 100 d (by simp [d]; unfold finiteWidth at hcap; omega)
  let e := d.setv rK (100*bits.length+100)
  have he : e.val rR=0 := by
    simp only [e,d,b,WState.setv_val,
      Function.update_of_ne hRK,Function.update_of_ne hRG,hz]
  have e4 := incN_spec cap rR 3 e (by rw [he]; omega)
  rw [he,Nat.zero_add] at e4
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap ?_ ?_
  · apply WState.eq
    · rfl
    · rfl
    · funext reg
      simp only [e,d,b,WState.setv_val,Function.update_apply,hz,stA,regsOf,finiteWidth]
      split_ifs <;> simp_all [rR,rK,rG,rT,rC1]
      omega
    · rfl
  · unfold finiteSetupACost
    omega

end NearQuarticWires.StageFormulaMetadata
