import Proof.Quartic.StagePrintTuple.StackContract
import Proof.Wire_3_5.PrimAsmCopyNat

set_option autoImplicit false

namespace NearQuarticWires.StageStackInput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: every cached
field is physically copied with its outer markers and source-head reset. -/
def cachedFramesProgram (sources : List (Fin (ns+1))) (dst : Fin (ns+1))
    (OP SC : Fin nr) : WM ns nr :=
  match sources with
  | []=>.skip
  | src::tail=>.seq (appendMarkedFrameReset src dst OP SC) (cachedFramesProgram tail dst OP SC)

def cachedFramesBytes (bits : List (List Bool)) : List Bool :=
  bits.flatMap fun w=>marks (frame w)

def cachedFramesCost : List (List Bool)→ℕ
  | []=>0
  | bits::tail=>appendMarkedFrameCost bits+cachedFramesCost tail+1

/-- `lem:print` and `prop:time`, paper/paper.tex: repeated cached sources are read anew, with every real
rewind charged; the actual source bytes are never replaced by constants. -/
theorem cachedFramesProgram_spec (cap : ℕ) (dst : Fin (ns+1)) (OP SC : Fin nr)
    (hOS : OP≠SC) (fields : List (Fin (ns+1)×List Bool))
    (hsrc : ∀p∈fields,p.1≠dst) (σ : WState ns nr)
    (hdata : ∀p∈fields,σ.st p.1=frame p.2 ∧ σ.sh p.1=0)
    (hd : σ.sh dst=(σ.st dst).length) (hSC : σ.val SC=0)
    (hcap : σ.val OP+(cachedFramesBytes (fields.map Prod.snd)).length+1≤cap) :
    WExec cap (cachedFramesProgram (fields.map Prod.fst) dst OP SC) σ
      (appendO σ dst OP (cachedFramesBytes (fields.map Prod.snd)))
      (cachedFramesCost (fields.map Prod.snd)) := by
  induction fields generalizing σ with
  | nil =>
      simpa only [List.map_nil,cachedFramesProgram,cachedFramesBytes,List.flatMap_nil,
        appendO_nil,cachedFramesCost] using (WExec.skip (cap:=cap) σ)
  | cons p tail ih =>
      have hp:=hdata p (by simp)
      have hpd:=hsrc p (by simp)
      have e1:=appendMarkedFrameReset_spec cap p.1 dst OP SC hpd hOS p.2 [] σ
        (by simpa only [List.append_nil] using hp.1) hp.2 hd hSC (by
          simp only [cachedFramesBytes,List.map_cons,List.flatMap_cons,List.length_append,
            Codec.marks_length] at hcap
          omega)
      let d:=appendO σ dst OP (marks (frame p.2))
      have e2:=ih (fun q hq=>hsrc q (by simp [hq])) d (by
        intro q hq
        have hqdata:=hdata q (by simp [hq])
        have hqd:=hsrc q (by simp [hq])
        simpa only [d,appendO,WState.setv_st,WState.seth_st,WState.sets_st,
          Function.update_of_ne hqd,WState.setv_sh,WState.seth_sh,WState.sets_sh] using hqdata)
        (by simp [d,appendO,hd]) (by simp [d,appendO,hOS.symm,hSC]) (by
          simp only [d,appendO_val,Function.update_self]
          simp only [cachedFramesBytes,List.map_cons,List.flatMap_cons,List.length_append] at hcap
          dsimp [cachedFramesBytes]
          omega)
      refine (e1.seq e2).cast cap ?_ ?_
      · simp only [d,appendO_append,cachedFramesBytes,List.map_cons,List.flatMap_cons]
      · simp only [List.map_cons,cachedFramesCost]
        omega

end NearQuarticWires.StageStackInput
