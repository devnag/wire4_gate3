import Proof.Quartic.StageGreedyCollector.BatchFramer
import Proof.Gates.CounterMachine.TabCallDock

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.CounterMachine

variable {R : Type} {input : R→List Bool} {source : R→BatchSource} {budget : R→ℕ}

def frameAfterMap (t : ℕ) (j : Fin t) : Fin (t+2) := j.castAdd 2

def frameAfterOut (t : ℕ) : Fin (t+2) := ⟨t,by omega⟩

def frameAfterRuler (t : ℕ) : Fin (t+2) := ⟨t+1,by omega⟩

theorem frameAfterMap_injective (t : ℕ) : Function.Injective (frameAfterMap t) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (t+2)=>x.val) h)

theorem frameAfterMap_ne_out (t : ℕ) (j : Fin t) : frameAfterMap t j≠frameAfterOut t := by
  intro h
  have hh:=congrArg Fin.val h
  change j.val=t at hh
  have :=j.isLt
  omega

theorem frameAfterMap_ne_ruler (t : ℕ) (j : Fin t) : frameAfterMap t j≠frameAfterRuler t := by
  intro h
  have hh:=congrArg Fin.val h
  change j.val=t+1 at hh
  have :=j.isLt
  omega

/-- `lem:print`, paper/paper.tex: the actual
raw batch producer runs once in its own bank, followed by the structural
header, count and request-pair framing pass on its real output. -/
noncomputable def frameAfterProgram
    (f : WordFunction R input (fun r=>(source r).word) budget) : WMX (f.program.tapeCount+1) 3 :=
  let t:=f.program.tapeCount
  .seq (.machZ f.program.machine (frameAfterMap t) (frameAfterRuler t))
    (.wm (frameBatch (frameAfterMap t f.program.outputTape) (frameAfterOut t) 0 1 2))

def frameAfterCost (r : R) : ℕ := 2*budget r+100*((source r).word.length+(source r).words.length+1)+3

def frameAfterLens (t b : ℕ) (i : Fin (t+2)) : ℕ := if i.val=t+1 then b else 0

/-- `lem:print` and `prop:time`, paper/paper.tex: the ordinary raw producer and the linear framing
pass form one physical computation, with the actual call reset charged. -/
theorem frameAfter_run (f : WordFunction R input (fun r=>(source r).word) budget) (r : R) :
    ∃ b, WXExec (source r).frameCapacity (frameAfterProgram f)
      (idealStart (f.program.tapeCount+1) 3 (input r)
        (frameAfterLens f.program.tapeCount (budget r))) b
      (frameAfterCost (source:=source) (budget:=budget) r) ∧
      b.st (frameAfterOut f.program.tapeCount)=frame (source r).word := by
  let t:=f.program.tapeCount
  let a:=idealStart (t+1) 3 (input r) (frameAfterLens t (budget r))
  have ht : 2≤t:=f.program.twoTapes
  have hin : a.st (frameAfterMap t (tape0 f.program))=frame (input r) := by
    simp [a,idealStart,frameAfterMap,tape0]
  have hb : ∀ j,j≠tape0 f.program→a.st (frameAfterMap t j)=[] := by
    intro j hj
    have hj0 : j.val≠0:=fun h=>hj (Fin.ext h)
    have hjt:=j.isLt
    have hjz : (Fin.castAdd 2 j : Fin (t+2))≠0 := by
      intro hz
      exact hj0 (congrArg (fun x : Fin (t+2)=>x.val) hz)
    simp [a,idealStart,frameAfterMap,frameAfterLens,hjz,show j.val≠t+1 by omega]
  have hL : a.st (frameAfterRuler t)=List.replicate (budget r) false := by
    simp [a,idealStart,frameAfterRuler,frameAfterLens]
  obtain ⟨b,eb,hout,hh,hoff,hv⟩:=wfDock_exact f r (source r).frameCapacity
    (frameAfterMap t) (frameAfterMap_injective t) (frameAfterRuler t)
    (frameAfterMap_ne_ruler t) a hin hb (fun _=>rfl) (budget r) hL rfl le_rfl
  have hbo:=hoff (frameAfterOut t) (frameAfterMap_ne_out t)
  have hos : b.st (frameAfterOut t)=[] := by
    rw [hbo.1]
    simp [a,idealStart,frameAfterOut,frameAfterLens,show t≠0 by omega]
  have hoh : b.sh (frameAfterOut t)=0:=hbo.2
  have ef:=frameBatch_spec (source r).frameCapacity
    (frameAfterMap t f.program.outputTape) (frameAfterOut t) (0 : Fin 3) 1 2
    (frameAfterMap_ne_out t _) (by decide) (by decide) (by decide)
    (source r).header (source r).count (source r).words [] b
    (by simpa only [List.nil_append,BatchSource.word] using hout) (hh _)
    (by rw [hos,hoh];rfl) (by rw [hv];rfl)
    (by rw [hv];change 0+2*(source r).word.length+1≤(source r).frameCapacity
        unfold BatchSource.frameCapacity;omega)
    (by rw [hv];change 0+(source r).word.length≤(source r).frameCapacity
        unfold BatchSource.frameCapacity;omega)
  refine ⟨_,(WXExec.seq eb (WXExec.wm ef)).mono ?_,?_⟩
  · dsimp [frameAfterCost,BatchSource.word]
    omega
  · change (appendO (adv _ _ _ _ b _ _) (frameAfterOut t) 0 [false]).st (frameAfterOut t)=_
    simp only [appendO,adv,WState.setv_st,WState.seth_st,WState.sets_st,Function.update_self]
    rw [hos,List.nil_append]
    exact (NearCubicGates.Close.Codec.frame_eq_marks (source r).word).symm

/-- `lem:print` and `prop:time`, paper/paper.tex: a raw batch producer is physically framed before the
next ordinary call; no output-length oracle or uncharged conversion is used. -/
noncomputable def frameAfterWordFunction
    (f : WordFunction R input (fun r=>(source r).word) budget) :
    WordFunction R input (fun r=>frame (source r).word)
      (fun r=>2*frameAfterCost (source:=source) (budget:=budget) r+2) :=
  wordFunction_of_ideal (frameAfterProgram f) (frameAfterOut f.program.tapeCount)
    (by simp [frameAfterOut];have :=f.program.twoTapes;omega)
    (fun r=>(source r).frameCapacity) (fun r=>frameAfterLens f.program.tapeCount (budget r))
    (frameAfterCost (source:=source) (budget:=budget)) (fun _=>le_rfl) (by
      intro r
      refine ⟨?_,frameAfter_run f r⟩
      simp [frameAfterLens,frameAfterOut])

end NearQuarticWires.StageGreedyCollector
