import Proof.Quartic.StageNativeKidsTail.Request
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsTail

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.CounterMachine
open StageNativeKids StageResize

abbrev ResizeCallee := WordFunction StreamResizeRequest StreamResizeRequest.word
  StreamResizeRequest.output StreamResizeRequest.budget

def bank (t : ℕ) (j : Fin t) : Fin (t+4) := ⟨j.val+2,by omega⟩
def ruler (t : ℕ) : Fin (t+4) := ⟨t+2,by omega⟩
def out (t : ℕ) : Fin (t+4) := ⟨t+3,by omega⟩

theorem bank_injective (t : ℕ) : Function.Injective (bank t) := by
  intro i j h
  apply Fin.ext
  have hv:=congrArg Fin.val h
  dsimp [bank] at hv
  omega

theorem bank_ne_ruler (t : ℕ) (j : Fin t) : bank t j≠ruler t := by
  intro he
  have h:=congrArg Fin.val he
  dsimp [bank,ruler] at h
  omega

theorem bank_off (t : ℕ) (j : Fin t) : bank t j≠(0 : Fin (t+4)) ∧
    bank t j≠(1 : Fin (t+4)) ∧ bank t j≠out t := by
  constructor
  · intro he;have h:=congrArg Fin.val he;simp only [bank,Fin.val_zero] at h;omega
  · constructor
    · intro he;have h:=congrArg Fin.val he;simp only [bank,Fin.val_one] at h;omega
    · intro he;have h:=congrArg Fin.val he;dsimp [bank,out] at h;omega

def capacity (r : ResizeTailRequest) : ℕ := 10*(r.word.length+r.stream.output.length+1)+10

def lens (t b : ℕ) (i : Fin (t+4)) : ℕ := if i.val=t+2 then b else 0

noncomputable def start (f : ResizeCallee) (r : ResizeTailRequest) : WState (f.program.tapeCount+3) 5 :=
  idealStart _ 5 r.word (lens f.program.tapeCount r.stream.budget)

noncomputable def loaded (f : ResizeCallee) (r : ResizeTailRequest) : WState (f.program.tapeCount+3) 5 :=
  (((start f r).sets 1 r.word).seth 0 (2*r.word.length+1))

/-- `lem:print`, paper/paper.tex: the real
outer request is unframed onto a separate source tape, preserving
its original binary count and all stream bytes. -/
theorem load_run (f : ResizeCallee) (r : ResizeTailRequest) :
    WExec (capacity r) (StageGamma.unframeRecord 0 1 4) (start f r) (loaded f r)
      (23*r.word.length+5) := by
  have e:=StageGamma.unframeRecord_run (capacity r) (0 : Fin (f.program.tapeCount+4)) 1
    (by have h:=f.program.twoTapes;intro he;have hh:=congrArg Fin.val he;norm_num at hh)
    4 r.word [] [] (start f r) (by simp [start,idealStart]) rfl
    (by simp [start,idealStart,lens]) rfl
    (by unfold capacity;omega)
  simpa [loaded,start,idealStart,lens] using e

end NearQuarticWires.StageNativeKidsTail
