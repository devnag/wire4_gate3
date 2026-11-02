import Proof.Quartic.StageNativeKidsTail.Layout
import Proof.Quartic.StagePrintTuple.NaturalsCopy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsTail

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Expand.PolyTab NearCubicGates.Close.Recovery.HTParts
open StageNativeKids StageResize StageTuple

theorem out_ne_raw (t : ℕ) : out t≠(1 : Fin (t+4)) := by
  intro he
  have h:=congrArg Fin.val he
  simp only [out,Fin.val_one] at h
  omega

theorem loaded_bank (f : ResizeCallee) (r : ResizeTailRequest) (j : Fin f.program.tapeCount) :
    (loaded f r).st (bank f.program.tapeCount j)=[] := by
  have hz : (bank f.program.tapeCount j).val≠0 := by dsimp [bank];omega
  have hl : (bank f.program.tapeCount j).val≠f.program.tapeCount+2 := by
    have hj:=j.isLt
    dsimp [bank]
    omega
  simp [loaded,start,idealStart,lens,(bank_off _ j).2.1,hz,hl,(bank_off _ j).1]

theorem loaded_out (f : ResizeCallee) (r : ResizeTailRequest) :
    (loaded f r).st (out f.program.tapeCount)=[] := by
  simp [loaded,start,idealStart,lens,out,out_ne_raw]

theorem loaded_out_head (f : ResizeCallee) (r : ResizeTailRequest) :
    (loaded f r).sh (out f.program.tapeCount)=0 := by
  simp [loaded,start,idealStart,out]

noncomputable def counted (f : ResizeCallee) (r : ResizeTailRequest) :
    WState (f.program.tapeCount+3) 5 :=
  adv 1 (out f.program.tapeCount) 0 1 (loaded f r) (marks (countWord r)) (countWord r).length

def copyCount (t : ℕ) : WM (t+3) 5 := copyNaturalFields 1 1 (out t) 0 1 2

/-- `lem:print`, paper/paper.tex: the first
binary row-count codec is copied literally into the final reply's
markers, without enumerating or reconstructing its numeric value. -/
theorem copyCount_run (f : ResizeCallee) (r : ResizeTailRequest) :
    WExec (capacity r) (copyCount f.program.tapeCount) (loaded f r) (counted f r)
      (28*(countWord r).length+1) := by
  have hc:=countWord_length_le r
  have e:=copyNaturalFields_spec (capacity r) (1 : Fin (f.program.tapeCount+4))
    (out f.program.tapeCount) 0 1 2 (out_ne_raw _).symm (by decide) (by decide) (by decide)
    [r.stream.rows.length] [] r.stream.word (loaded f r)
    (by simp only [loaded,WState.seth_st,WState.sets_st,Function.update_self,List.nil_append,
        List.flatMap_cons,List.flatMap_nil,List.append_nil,ResizeTailRequest.word,countWord])
    (by simp [loaded,start,idealStart])
    (by rw [loaded_out,loaded_out_head];rfl) rfl
    (by simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,
          show (loaded f r).val 0=0 from rfl]
        change 0+2*(countWord r).length≤capacity r
        unfold capacity;omega)
    (by simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,
          show (loaded f r).val 1=0 from rfl]
        change 0+(countWord r).length<capacity r+1
        unfold capacity;omega)
  simpa only [copyCount,counted,List.length_singleton,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.length_nil,List.nil_append,countWord] using e

end NearQuarticWires.StageNativeKidsTail
