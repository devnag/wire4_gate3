import Proof.Quartic.StageCertificateControl.ExtendedBank
import Proof.Quartic.Control.Call

/-!
# A reusable physical call for the whole-test count

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

variable {ns : ℕ}

/-- `prop:time`, paper/paper.tex: one count
call is followed by an actual binary read, explicit return, and bank erase. -/
noncomputable def countCallProgram {p : Program} (s : Site p ns 16) : WMX ns 16 :=
  .seq (callP s) (.seq (.wm (readCountHeader (s.bank p.outputTape))) (cleanP s))

/-- `prop:time`, paper/paper.tex: the count
header's physical decoding and head return have their literal source cost. -/
def countHeaderReadCost (T : ℕ) : ℕ :=
  (natBitLength T+2)*(40*2^natBitLength T+40)+60*T+155*natBitLength T+101

/-- `prop:time`, paper/paper.tex: count-bank
setup, actual execution, header decoding and full cleanup are all charged. -/
def countCallCost (inputLength budget T : ℕ) : ℕ :=
  200*(inputLength+budget+1)+countHeaderReadCost T+10

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the actual framed count is retained in register 14,
all bank heads return to zero, and the bank is erased before reuse. -/
theorem countCall_exec {Request : Type} {input : Request→List Bool}
    {count budget : Request→ℕ}
    (f : WordFunction Request input (fun r => frame (RepairRepresentation.natWord (count r))) budget)
    (req : Request) (cap : ℕ) (s : Site f.program ns 16)
    (hregs : s.regs=StagePrint.poolSiteRegs) (σ : WState ns 16)
    (hin : ∀j,σ.st (s.bank j)=f.program.inputTapes (input req) j)
    (h0 : ∀j,σ.sh (s.bank j)=0)
    (hTL : σ.st s.tally=[]) (hTLh : σ.sh s.tally=0)
    (hG : σ.st s.guard=[]) (hGh : σ.sh s.guard=0)
    (hL : Worker.Blank (σ.st s.ruler)) (hLh : σ.sh s.ruler=0)
    (hR : ∀i,σ.val (s.regs i)=0)
    (h5 : σ.val 5=0) (h14 : σ.val 14=0)
    (hcap : 2*(input req).length+2+budget req≤cap)
    (hheader : 2^(natBitLength (count req)+1)+count req+4*natBitLength (count req)+4≤cap) :
    ∃ (tapes : Fin f.program.tapeCount→List Bool) (steps : ℕ) (τ : WState ns 16),
      steps≤budget req ∧
      WXExec cap (countCallProgram s) σ τ (countCallCost (input req).length (budget req) (count req)) ∧
      SimW (cleanState s ((calledState s σ tapes (input req).length steps).setv 14 (count req))) τ := by
  obtain ⟨tapes,steps,τ,ht,hsteps,_,hfar,ec,hs⟩ :=
    callP_exec f req cap s σ hin h0 hTL hTLh hG hGh hL hLh hR hcap
  let cs := calledState s σ tapes (input req).length steps
  have csBank (j) : cs.st (s.bank j)=tapes j := by
    simp only [cs,calledState,WState.sets_st,Function.update_of_ne (s.guard_ne j),
      Function.update_of_ne (s.tally_ne j)]
    exact updS_st_slot s.bank σ (fun _ => 0) tapes s.bank_inj j
  have csHead (j) : cs.sh (s.bank j)=0 :=
    updS_sh_slot s.bank σ (fun _ => 0) tapes s.bank_inj j
  have csV (i : Fin 16) : cs.val i=σ.val i := rfl
  have hRV (i : Fin 4) : σ.val (StagePrint.poolSiteRegs i)=0 := by rw [← hregs];exact hR i
  have er := readCountHeader_spec cap cs (s.bank f.program.outputTape) (count req)
    (by rw [csBank,ht]) (csHead _)
    (by have hz := hRV 0;change σ.val (0 : Fin 16)=0 at hz;exact hz)
    (by have hz := hRV 1;change σ.val (1 : Fin 16)=0 at hz;exact hz)
    (by have hz := hRV 2;change σ.val (2 : Fin 16)=0 at hz;exact hz)
    (by have hz := hRV 3;change σ.val (3 : Fin 16)=0 at hz;exact hz)
    (by rw [csV];exact h5) (by rw [csV];exact h14) hheader
  let decoded := cs.setv 14 (count req)
  have hdecodedHead (j) : decoded.sh (s.bank j)=0 := csHead j
  have dT : decoded.st s.tally=List.replicate steps true := by
    simp [decoded,cs,calledState,Function.update_of_ne s.tally_guard]
  have dTh : decoded.sh s.tally=0 := by
    simp [decoded,cs,calledState,updS_sh_other _ _ _ _ _ s.tally_ne,hTLh]
  have dG : decoded.st s.guard=List.replicate (guardLength (input req).length steps) true := by
    simp [decoded,cs,calledState]
  have dGh : decoded.sh s.guard=0 := by
    simp [decoded,cs,calledState,updS_sh_other _ _ _ _ _ s.guard_ne,hGh]
  have dL : decoded.st s.ruler=σ.st s.ruler := by
    simp only [decoded,cs,calledState,WState.setv_st,WState.sets_st,
      Function.update_of_ne s.guard_ruler.symm,Function.update_of_ne s.tally_ruler.symm]
    exact updS_st_other s.bank σ (fun _ => 0) tapes s.ruler s.ruler_ne
  have dLh : decoded.sh s.ruler=0 := by
    simp [decoded,cs,calledState,updS_sh_other _ _ _ _ _ s.ruler_ne,hLh]
  have dR : decoded.val (s.regs 0)=0 := by
    have hn : s.regs 0≠(14 : Fin 16) := by rw [hregs];decide
    simpa only [decoded,WState.setv_val,Function.update_of_ne hn,csV] using hR 0
  obtain ⟨τclean,ee,hsc⟩ := cleanP_exec cap s (guardLength (input req).length steps) decoded
    (by intro j q hq;change readTapeBit (cs.st (s.bank j)) q=false;rw [csBank];exact hfar j q hq)
    hdecodedHead
    (by intro q hq;rw [dT];exact readTapeBit_beyond _ _ (by simp;unfold guardLength at hq;omega))
    dTh dG dGh (by rw [dL];exact hL) dLh dR (by unfold guardLength;omega)
  obtain ⟨τread,erActual,hsRead⟩ := wxexec_sim (WXExec.wm er) τ hs
  obtain ⟨τfinal,eeActual,hsFinal⟩ := wxexec_sim ee τread hsRead
  refine ⟨tapes,steps,τfinal,hsteps,?_,SimW.trans hsc hsFinal⟩
  refine (ec.seq (erActual.seq eeActual)).mono ?_
  unfold countCallCost countHeaderReadCost callCost cleanCost guardLength
  omega

end NearQuarticWires.StageCertificateControl
