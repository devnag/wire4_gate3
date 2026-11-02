import Proof.Quartic.StageCertificateControl.CountState

/-!
# Cold preparation to the counted native-table loop

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.WorkerArith (inTape)
open NearQuarticWires.Control

/-- `prop:time`, paper/paper.tex: the count
bootstrap includes one original-source copy, one real count call, all
binary decoding work, and complete reusable-bank cleanup. -/
def poolCountCost (inputLength budget T : ℕ) : ℕ :=
  400*(inputLength+budget+1)+countHeaderReadCost T+100

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: from the literal cold preparation, the actual
count computation produces the unchanged native-loop start state.
Every copied byte, arithmetic read, tape return and bank erase is paid. -/
theorem poolCount_exec {Request : Type} {input : Request→List Bool}
    {count budget : Request→ℕ}
    (f : WordFunction Request input (fun r => frame (RepairRepresentation.natWord (count r))) budget)
    (p : Program) (hq : f.program.tapeCount≤p.tapeCount) (req : Request)
    (cache : ℕ→List Bool) (cap : ℕ)
    (hcopy : 4*(input req).length+4≤cap)
    (hcall : 2*(input req).length+2+budget req≤cap)
    (hheader : 2^(natBitLength (count req)+1)+count req+4*natBitLength (count req)+4≤cap) :
    ∃ τ, WXExec cap (poolCountProgram p f.program hq)
      (startState (p.tapeCount+5) 16 (input req)) τ
      (poolCountCost (input req).length (budget req) (count req)) ∧
      SimW (StagePrint.poolState p (input req) cache 0 (count req)) τ := by
  let s := countBankSite p f.program hq
  let σ := startState (p.tapeCount+5) 16 (input req)
  let a := countLoadedState p f.program hq (input req)
  have hinput0 : s.input≠(0 : Fin (p.tapeCount+6)) := (countBankSite_input_ne p f.program hq).1
  have hinputT : s.input≠s.tally := s.tally_ne _
  have hinputG : s.input≠s.guard := s.guard_ne _
  have hinputL : s.input≠s.ruler := s.ruler_ne _
  have hinputV : s.input.val≠0 := by intro h;exact hinput0 (Fin.ext h)
  have ec := copyRW_spec cap (StagePrint.poolSource p) s.input hinput0.symm
    (8 : Fin 16) 9 10 (by decide) (by decide) (by decide) (input req) [] σ
    (by simp [σ,startState,StagePrint.poolSource]) rfl
    (by change (if s.input.val=0 then frame (input req) else [])=[];rw [if_neg hinputV])
    rfl rfl rfl rfl hcopy
  have hinputs (j : Fin f.program.tapeCount) : a.st (s.bank j)=f.program.inputTapes (input req) j := by
    by_cases hj : j=inTape f.program
    · subst j
      change (σ.sets s.input (frame (input req))).st s.input=frame (input req)
      simp
    · have hne : s.bank j≠s.input := fun h => hj (s.bank_inj h)
      have hv : (s.bank j).val≠0 := by change 5+j.val≠0;omega
      have hjv : j.val≠0 := by intro h;apply hj;apply Fin.ext;exact h
      change (σ.sets s.input (frame (input req))).st (s.bank j)=_
      rw [WState.sets_st,Function.update_of_ne hne]
      change (if (s.bank j).val=0 then frame (input req) else [])=
        if j.val=0 then frame (input req) else []
      rw [if_neg hv,if_neg hjv]
  have hTL : a.st s.tally=[] := by
    change (σ.sets s.input (frame (input req))).st s.tally=[]
    rw [WState.sets_st,Function.update_of_ne hinputT.symm]
    rfl
  have hG : a.st s.guard=[] := by
    change (σ.sets s.input (frame (input req))).st s.guard=[]
    rw [WState.sets_st,Function.update_of_ne hinputG.symm]
    rfl
  have hL : a.st s.ruler=[] := by
    change (σ.sets s.input (frame (input req))).st s.ruler=[]
    rw [WState.sets_st,Function.update_of_ne hinputL.symm]
    rfl
  obtain ⟨tapes,steps,τ,hsteps,er,hs⟩ := countCall_exec f req cap s rfl a hinputs
    (fun _ => rfl) hTL rfl hG rfl (by rw [hL];exact nil_blank) rfl
    (fun _ => rfl) rfl rfl hcall hheader
  refine ⟨τ,(WXExec.wm ec |>.seq er).mono ?_,?_⟩
  · unfold poolCountCost countCallCost
    omega
  · rw [countCleared_state p f.program hq (input req) cache (count req) steps tapes] at hs
    exact hs

end NearQuarticWires.StageCertificateControl
