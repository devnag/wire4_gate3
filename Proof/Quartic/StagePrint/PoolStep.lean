import Proof.Quartic.StagePrint.IndexedInput
import Proof.Quartic.StagePrint.CallStates

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: one original occurrence is indexed, computed, appended, and followed by the next index. -/
noncomputable def poolOccurrence {p : Program} (s : Site p ns nr) (IN POOL : Fin (ns+1))
    (R : Fin 8 ↪ Fin nr) (C OP : Fin nr) : WMX ns nr :=
  .seq (writeIndexedInput IN s.input R C)
    (.seq (callAppendProgram s POOL OP) (WMX.inc (R 0)))

/-- `prop:time`, paper/paper.tex: occurrence indexing, exact original children and complete bank reuse all contribute to the pool clock. -/
def poolOccurrenceCost (index sourceLength inputLength budget : ℕ) : ℕ :=
  writeIndexedCost index sourceLength+callAppendCost inputLength budget+10

/-- `lem:print`, paper/paper.tex: a complete reusable original-occurrence body constructs its own callee input and returns an empty work bank, retaining all emitted children. -/
theorem poolOccurrence_exec {Request : Type} {input cache : Request→List Bool} {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>frame (cache r)) budget) (req : Request) (cap : ℕ)
    (s : Site f.program ns nr) (IN POOL : Fin (ns+1)) (R : Fin 8 ↪ Fin nr) (C OP : Fin nr)
    (hINB : ∀j,s.bank j≠IN) (hpB : ∀j,s.bank j≠POOL)
    (hpT : POOL≠s.tally) (hpG : POOL≠s.guard) (hpL : POOL≠s.ruler)
    (hCR : ∀i,C≠R i) (hOS : OP≠s.regs 0) (hOI : OP≠R 0)
    (σ : WState ns nr) (v : ℕ) (w : List Bool)
    (hinput : input req=NearCubicWires.RepairRepresentation.natWord v++w)
    (hb : ∀j,σ.st (s.bank j)=[]) (hh : ∀j,σ.sh (s.bank j)=0)
    (hTL : σ.st s.tally=[]) (hTLh : σ.sh s.tally=0)
    (hG : σ.st s.guard=[]) (hGh : σ.sh s.guard=0)
    (hL : Worker.Blank (σ.st s.ruler)) (hLh : σ.sh s.ruler=0)
    (hS : ∀i,σ.val (s.regs i)=0)
    (hv : σ.val (R 0)=v) (hz : ∀i,i≠0→σ.val (R i)=0) (hC : σ.val C=0)
    (hIN : σ.st IN=frame w) (hINh : σ.sh IN=0)
    (hp : σ.sh POOL=(σ.st POOL).length)
    (hwrite : v+8*natBitLength v+4*w.length+20≤cap)
    (hcall : 2*(input req).length+2+budget req≤cap)
    (hcopy : σ.val OP+(frame (cache req)).length+1≤cap) :
    ∃ τ, WXExec cap (poolOccurrence s IN POOL R C OP) σ τ
      (poolOccurrenceCost v w.length (input req).length (budget req)) ∧
      SimW ((appendO σ POOL OP (frame (cache req))).setv (R 0) (v+1)) τ := by
  have ewrite:=writeIndexedInput_exec cap IN s.input R C
    (hINB _).symm hCR σ v w hv hz hC hIN hINh (hb _) (hh _) hwrite
  rw [←hinput] at ewrite
  let σ1:=σ.sets s.input (frame (input req))
  have h1in : ∀j,σ1.st (s.bank j)=f.program.inputTapes (input req) j := by
    intro j
    by_cases hj : j=NearCubicGates.Close.WorkerArith.inTape f.program
    · subst hj
      simp [σ1,Site.input,Program.inputTapes,NearCubicGates.Close.WorkerArith.inTape]
    · have hneq : s.bank j≠s.input := s.bank_inj.ne hj
      have hj0 : j.val≠0 := by
        intro h
        exact hj ((NearCubicGates.Close.WorkerArith.inTape_iff f.program j).2 h)
      simp [σ1,hneq,Program.inputTapes,hj0,hb]
  have h1TL : σ1.st s.tally=[] := by
    simp [σ1,Site.input,(s.tally_ne _).symm,hTL]
  have h1G : σ1.st s.guard=[] := by
    simp [σ1,Site.input,(s.guard_ne _).symm,hG]
  have h1L : Worker.Blank (σ1.st s.ruler) := by
    simpa [σ1,Site.input,(s.ruler_ne _).symm] using hL
  have h1p : σ1.sh POOL=(σ1.st POOL).length := by
    simpa [σ1,Site.input,(hpB _).symm] using hp
  obtain ⟨tapes,steps,τc,hsteps,ecall,hsc⟩:=callAppend_exec f req cap s POOL OP hpB hpT hpG hOS σ1
    h1in hh h1TL hTLh h1G hGh h1L hLh hS hpL h1p hcall hcopy
  have hclean : cleanState s σ1=σ := by
    change cleanState s (σ.sets (s.bank (NearCubicGates.Close.WorkerArith.inTape f.program))
      (frame (input req)))=σ
    rw [cleanState_set_bank,cleanState_self s σ hb hh hTL hG]
  rw [callAppendPost_eq s σ1 tapes (input req).length steps POOL OP (frame (cache req)) hpB hpT hpG,
    hclean] at hsc
  let ideal:=appendO σ POOL OP (frame (cache req))
  have hi : ideal.val (R 0)=v := by
    simp [ideal,appendO,hOI.symm,hv]
  have einc:=WXExec.inc cap (R 0) ideal (by rw [hi];omega)
  rw [hi] at einc
  obtain ⟨τ,eactual,hsfinal⟩:=wxexec_sim einc τc hsc
  refine ⟨τ,(WXExec.seq ewrite (WXExec.seq ecall eactual)).mono ?_,hsfinal⟩
  unfold poolOccurrenceCost
  omega

end NearQuarticWires.StagePrint
