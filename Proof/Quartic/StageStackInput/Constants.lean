import Proof.Quartic.StageStackInput.CachedFrames
import Proof.Quartic.StageStackInput.Layout

set_option autoImplicit false

namespace NearQuarticWires.StageStackInput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close
open NearCubicGates.Close.WordPrograms.SInt (encS)
open StageTuple

variable {ns nr : ℕ}

def cacheSources (P : Fin 5↪Fin (ns+1)) : List (Fin (ns+1)) := [P 1,P 1,P 1,P 2,P 3]

def cacheFields (P : Fin 5↪Fin (ns+1)) (r : StagePrint.StackRequest) :
    List (Fin (ns+1)×List Bool) :=
  [(P 1,frame (binary (r.W+1) 0)),(P 1,frame (binary (r.W+1) 0)),
    (P 1,frame (binary (r.W+1) 0)),(P 2,frame (binary (r.W+1) (encS r.coefficient))),
    (P 3,frame (binary (r.W+1) 2))]

theorem constantCost (r : StagePrint.StackRequest) :
    cachedFramesCost (constantFields r)=2000*r.W+4005 := by
  simp only [constantFields,cachedFramesCost,appendMarkedFrameCost,
    frame_length,binary_length]
  omega

/-- `lem:print`, paper/paper.tex: the five actual
cached source fields are read in the exact Stack order, including all
three physical copies of the same zero cache and their source rewinds. -/
theorem copyConstants_spec (cap : ℕ) (P : Fin 5↪Fin (ns+1)) (OP SC : Fin nr)
    (hOS : OP≠SC) (r : StagePrint.StackRequest) (σ : WState ns nr)
    (hz : σ.st (P 1)=frame (frame (binary (r.W+1) 0)))
    (hc : σ.st (P 2)=frame (frame (binary (r.W+1) (encS r.coefficient))))
    (ht : σ.st (P 3)=frame (frame (binary (r.W+1) 2)))
    (hzh : σ.sh (P 1)=0) (hch : σ.sh (P 2)=0) (hth : σ.sh (P 3)=0)
    (hd : σ.sh (P 4)=(σ.st (P 4)).length) (hSC : σ.val SC=0)
    (hcap : σ.val OP+40*r.W+71≤cap) :
    WExec cap (cachedFramesProgram (cacheSources P) (P 4) OP SC) σ
      (appendO σ (P 4) OP (cachedFramesBytes (constantFields r)))
      (cachedFramesCost (constantFields r)) := by
  have hsrc : ∀p∈cacheFields P r,p.1≠P 4 := by
    intro p hp
    simp only [cacheFields,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl <;> exact P.injective.ne (by decide)
  have hdata : ∀p∈cacheFields P r,σ.st p.1=frame p.2 ∧ σ.sh p.1=0 := by
    intro p hp
    simp only [cacheFields,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl
    · exact ⟨hz,hzh⟩
    · exact ⟨hz,hzh⟩
    · exact ⟨hz,hzh⟩
    · exact ⟨hc,hch⟩
    · exact ⟨ht,hth⟩
  have hs : (cacheFields P r).map Prod.fst=cacheSources P := rfl
  have hb : (cacheFields P r).map Prod.snd=constantFields r := rfl
  have hlen : (cachedFramesBytes (constantFields r)).length=40*r.W+70 :=
    constantFields_length r
  have hh:=cachedFramesProgram_spec cap (P 4) OP SC hOS (cacheFields P r)
    hsrc σ hdata hd hSC (by rw [hb,hlen];omega)
  rw [hs,hb] at hh
  exact hh

end NearQuarticWires.StageStackInput
