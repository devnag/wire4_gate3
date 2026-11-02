import Proof.Quartic.StageGreedyCollector.BatchFrame
import Proof.Quartic.StageGamma.Unframe
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: the finite
actual batch consists of its common header, encoded count and ordered words. -/
structure BatchSource where
  header : List Bool
  count : ℕ
  words : List (List Bool)

def BatchSource.word (r : BatchSource) : List Bool := batchSource r.header r.count r.words

def batchFramer : WMX 2 3 :=
  .seq (.wm (StageGamma.unframeRecord 0 1 0)) (.wm (frameBatch 1 2 0 1 2))

def BatchSource.frameCost (r : BatchSource) : ℕ := 130*(r.word.length+r.words.length+1)

def BatchSource.frameCapacity (r : BatchSource) : ℕ := 2*r.word.length+10

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete cold framing machine reads its actual
finite source, copies every byte, and writes exactly one outer frame. -/
theorem batchFramer_run (r : BatchSource) :
    ∃ b, WXExec r.frameCapacity batchFramer (idealStart 2 3 r.word (fun _=>0)) b r.frameCost ∧
      b.st 2=frame r.word := by
  let a:=idealStart 2 3 r.word (fun _=>0)
  let b:=(a.sets 1 r.word).seth 0 (2*r.word.length+1)
  have e1 : WExec r.frameCapacity (StageGamma.unframeRecord 0 1 0) a b
      (23*r.word.length+5) := by
    simpa [a,b,idealStart] using
      StageGamma.unframeRecord_run r.frameCapacity (0 : Fin 3) 1 (by decide) (0 : Fin 3)
        r.word [] [] a (by simp [a,idealStart]) rfl rfl rfl (by unfold BatchSource.frameCapacity;omega)
  have e2:=frameBatch_spec r.frameCapacity (1 : Fin 3) 2 (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) (by decide) r.header r.count r.words [] b
    (by simp [b,BatchSource.word]) rfl rfl rfl
    (by change 0+2*r.word.length+1≤r.frameCapacity;unfold BatchSource.frameCapacity;omega)
    (by change 0+r.word.length≤r.frameCapacity;unfold BatchSource.frameCapacity;omega)
  refine ⟨_,(WXExec.seq (WXExec.wm e1) (WXExec.wm e2)).mono ?_,?_⟩
  · dsimp [BatchSource.frameCost,BatchSource.word]
    omega
  · change (appendO (adv (1 : Fin 3) 2 (0 : Fin 3) 1 b
      (r.word.flatMap fun bit=>[true,bit]) r.word.length) 2 0 [false]).st 2=frame r.word
    simp only [appendO,adv,WState.setv_st,WState.seth_st,WState.sets_st,Function.update_self]
    change ([]++r.word.flatMap (fun bit=>[true,bit]))++[false]=frame r.word
    simp only [List.nil_append]
    exact (NearCubicGates.Close.Codec.frame_eq_marks r.word).symm

/-- `lem:print` and `prop:time`, paper/paper.tex: the same finite program frames every actual batch,
with a budget linear in its bytes and number of requests. -/
noncomputable def batchFramerWordFunction :
    WordFunction BatchSource BatchSource.word (fun r=>frame r.word) (fun r=>2*r.frameCost+2) :=
  wordFunction_of_ideal batchFramer 2 (by decide) BatchSource.frameCapacity (fun _ _=>0)
    BatchSource.frameCost (fun _=>le_rfl) (by intro r;exact ⟨rfl,batchFramer_run r⟩)

end NearQuarticWires.StageGreedyCollector
