import Proof.Quartic.StageTupleMonomialFinish.FrameEnd
import Proof.Quartic.StagePrintTuple.KernelMaps
import Proof.Quartic.StagePrintTuple.MeasuredErase

set_option autoImplicit false

namespace NearQuarticWires.StageTupleMonomialFinish

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open StageTuple

/-- `lem:print`, paper/paper.tex: the two
coefficient caches are erased from their genuine starts, then only the
unparsed support tail is scanned before its full measured erasure. -/
def cachesProgram (span : ℕ) : WMX (span+29) 32 :=
  .seq (.wm (eraseFrameCache (kernelLocal span 15) 1))
    (.seq (.wm (eraseFrameCache (kernelLocal span 16) 1))
      (.seq (.wm (finishFrameCursor (kernelLocal span 14) 1))
        (.wm (eraseCacheBackward (kernelLocal span 14) 26))))

/-- `lem:print`, paper/paper.tex: coefficient
and support caches become reusable blanks while every other source,
output, history byte and persistent counter is retained. -/
def cachesState (span : ℕ) (σ : WState (span+29) 32) : WState (span+29) 32 :=
  (((((σ.sets (kernelLocal span 15) []).sets (kernelLocal span 16) []).sets
    (kernelLocal span 14) []).seth (kernelLocal span 14) 0).setv 26 0)

/-- `prop:time`, paper/paper.tex: cleanup
charges the two finite framed coefficients and the measured support
bytes, independently of all earlier output and tuple history. -/
def cachesCost (coefficient reply pre tail : List Bool) : ℕ :=
  60*((frame coefficient).length+1)+60*((frame reply).length+1)+
    40*((frame tail).length+1)+10*(pre++frame tail).length+4

/-- `lem:print` and `prop:time`, paper/paper.tex: actual cache cleanup preserves all exterior state and
uses register 26, already measured on the physical support frame. -/
theorem cachesProgram_spec (span cap : ℕ) (coefficient reply pre tail : List Bool)
    (σ : WState (span+29) 32)
    (hc : σ.st (kernelLocal span 15)=frame coefficient)
    (hch : σ.sh (kernelLocal span 15)=0)
    (hr : σ.st (kernelLocal span 16)=frame reply)
    (hrh : σ.sh (kernelLocal span 16)=0)
    (hs : σ.st (kernelLocal span 14)=pre++frame tail)
    (hsh : σ.sh (kernelLocal span 14)=pre.length)
    (hg : σ.st (kernelLocal span 28)=[]) (hgh : σ.sh (kernelLocal span 28)=0)
    (h0 : σ.val 0=0) (h1 : σ.val 1=0)
    (h26 : σ.val 26=(pre++frame tail).length)
    (hcc : (frame coefficient).length≤cap) (hrc : (frame reply).length≤cap)
    (hsc : (pre++frame tail).length≤cap) :
    ∃τ,WXExec cap (cachesProgram span) σ τ (cachesCost coefficient reply pre tail) ∧
      SimW (cachesState span σ) τ := by
  have kl {i j : Fin 30} : kernelLocal span i=kernelLocal span j ↔ i=j :=
    (kernelLocal span).injective.eq_iff
  obtain ⟨a',ea,ha⟩ := eraseFrameCache_spec cap (kernelLocal span 15) (kernelLocal span 28) 1 0
    (by simp [kl]) (by decide) coefficient σ hc hch (by simp [hg,hgh])
    (by rw [h0];omega) h1 hcc
  let a := σ.sets (kernelLocal span 15) []
  obtain ⟨b',eb,hb⟩ := eraseFrameCache_spec cap (kernelLocal span 16) (kernelLocal span 28) 1 0
    (by simp [kl]) (by decide) reply a (by simp [a,kl,hr]) (by simp [a,hrh])
    (by simp [a,kl,hg,hgh]) (by simp [a,h0]) (by simp [a,h1]) hrc
  obtain ⟨b'',eb',hb'⟩ := wxexec_sim (WXExec.wm eb) a' ha
  let b := a.sets (kernelLocal span 16) []
  have hbb : SimW b b'' := SimW.trans hb hb'
  have ec := finishFrameCursor_spec cap (kernelLocal span 14) (kernelLocal span 28) 1 0
    (by simp [kl]) (by decide) tail pre [] b
    (by simp [b,a,kl,hs]) (by simp [b,a,hsh]) (by simp [b,a,kl,hg,hgh])
    (by simp [b,a,h0]) (by simp [b,a,h1]) (by simp only [List.length_append] at hsc;omega)
  obtain ⟨c',ec',hc'⟩ := wxexec_sim (WXExec.wm ec) b'' hbb
  let c := b.seth (kernelLocal span 14) (pre.length+(frame tail).length)
  obtain ⟨d',ed,hd⟩ := eraseMeasuredCache_spec cap (kernelLocal span 14) 26 (pre++frame tail) c
    (by simp [c,b,a,kl,hs]) (by simp [c]) (by simp [c,b,a,h26]) hsc
  obtain ⟨d'',ed',hd'⟩ := wxexec_sim (WXExec.wm ed) c' hc'
  have hfinal : (((c.sets (kernelLocal span 14) []).seth (kernelLocal span 14) 0).setv 26 0)=
      cachesState span σ := by
    apply WState.eq
    · funext i
      by_cases hi:i=kernelLocal span 14
      · subst i;simp [c,b,a,cachesState]
      · simp [c,b,a,cachesState,Function.update_of_ne hi]
    · rfl
    · rfl
    · rfl
  refine ⟨d'',?_,?_⟩
  · exact ((WXExec.wm ea).seq (eb'.seq (ec'.seq ed'))).mono (by unfold cachesCost;omega)
  · simpa only [hfinal] using SimW.trans hd hd'

end NearQuarticWires.StageTupleMonomialFinish
