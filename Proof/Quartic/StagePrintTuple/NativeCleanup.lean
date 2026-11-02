import Proof.Quartic.StagePrintTuple.KernelMaps
import Proof.Quartic.StagePrintTuple.MeasuredErase
import Proof.Quartic.StagePrintTuple.RecordEnd
import Proof.Quartic.StagePrintTuple.FrameErase

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: the completed
Cartesian step discards only its finite native reply and selected-atom
caches, using the two actual copied-byte counters and one real scan. -/
def nativeCleanupProgram (span : ℕ) : WMX (span+29) 32 :=
  .seq (.wm (eraseCacheBackward (kernelLocal span 18) 24))
    (.seq (.wm (finishRecordCursor (kernelLocal span 19) 1))
      (.seq (.wm (eraseCacheBackward (kernelLocal span 19) 25))
        (.wm (eraseFrameCache (kernelLocal span 17) 1))))

/-- `lem:print`, paper/paper.tex: the reusable
boundary keeps all tuple history, source and output bytes, and resets
only the three finite caches, their heads and measured-length registers. -/
def nativeCleanupState (span : ℕ) (σ : WState (span+29) 32) : WState (span+29) 32 :=
  let a := ((σ.sets (kernelLocal span 18) []).seth (kernelLocal span 18) 0).setv 24 0
  let b := ((a.sets (kernelLocal span 19) []).seth (kernelLocal span 19) 0).setv 25 0
  b.sets (kernelLocal span 17) []

/-- `prop:time`, paper/paper.tex: finite cache
cleanup is linear in actual copied native bytes and selected atom bytes;
it never scans an earlier tuple-history prefix or controller capacity. -/
def nativeCleanupCost (atom pre : List Bool) (records : List (List Bool)) : ℕ :=
  10*(frame (pre++records.flatMap frame)).length+1+
    (40*((records.flatMap frame).length+1))+1+
    (10*(pre++records.flatMap frame).length+1)+1+
    (60*((frame atom).length+1))+1

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual cleanup loop reaches the same blank cache
boundary for every signed native pool, including an empty child pool. -/
theorem nativeCleanupProgram_spec (span cap : ℕ) (atom pre : List Bool)
    (records : List (List Bool)) (hne : ∀record∈records,record≠[])
    (σ : WState (span+29) 32)
    (ha : σ.st (kernelLocal span 17)=frame atom) (hah : σ.sh (kernelLocal span 17)=0)
    (hf : σ.st (kernelLocal span 18)=frame (pre++records.flatMap frame))
    (hfh : σ.sh (kernelLocal span 18)=(frame (pre++records.flatMap frame)).length)
    (hr : σ.st (kernelLocal span 19)=pre++records.flatMap frame)
    (hrh : σ.sh (kernelLocal span 19)=pre.length)
    (hg : σ.st (kernelLocal span 28)=[]) (hgh : σ.sh (kernelLocal span 28)=0)
    (h0 : σ.val 0=0) (h1 : σ.val 1=0)
    (h24 : σ.val 24=(frame (pre++records.flatMap frame)).length)
    (h25 : σ.val 25=(pre++records.flatMap frame).length)
    (hfc : (frame (pre++records.flatMap frame)).length ≤ cap)
    (hrc : (pre++records.flatMap frame).length ≤ cap)
    (hac : (frame atom).length ≤ cap) :
    ∃τ,WXExec cap (nativeCleanupProgram span) σ τ (nativeCleanupCost atom pre records) ∧
      SimW (nativeCleanupState span σ) τ := by
  have kl {i j : Fin 30} : kernelLocal span i=kernelLocal span j ↔ i=j :=
    (kernelLocal span).injective.eq_iff
  obtain ⟨a',ea,ha'⟩ := eraseMeasuredCache_spec cap (kernelLocal span 18) 24
    (frame (pre++records.flatMap frame)) σ hf hfh h24 hfc
  let a := ((σ.sets (kernelLocal span 18) []).seth (kernelLocal span 18) 0).setv 24 0
  have eb := finishRecordCursor_spec cap (kernelLocal span 19) (kernelLocal span 28) 1 0
    (by simp [kl]) (by decide) records pre [] (by rfl) hne a
    (by simp [a,kl,hr]) (by simp [a,kl,hrh]) (by simp [a,kl,hg,hgh])
    (by simp [a,h0]) (by simp [a,h1])
    (by simp only [List.length_append] at hrc;omega)
  let b := a.seth (kernelLocal span 19) (pre.length+(records.flatMap frame).length)
  obtain ⟨b',eb',hb'⟩ := wxexec_sim (WXExec.wm eb) a' ha'
  obtain ⟨c',ec,hc'⟩ := eraseMeasuredCache_spec cap (kernelLocal span 19) 25
    (pre++records.flatMap frame) b (by simp [b,a,kl,hr])
    (by simp [b]) (by simp [b,a,h25]) hrc
  let c := ((b.sets (kernelLocal span 19) []).seth (kernelLocal span 19) 0).setv 25 0
  obtain ⟨c'',ec',hc''⟩ := wxexec_sim (WXExec.wm ec) b' hb'
  have hcc : SimW c c'' := SimW.trans hc' hc''
  obtain ⟨d,ed,hd⟩ := eraseFrameCache_spec cap (kernelLocal span 17) (kernelLocal span 28) 1 0
    (by simp [kl]) (by decide) atom c
    (by simp [c,b,a,kl,ha]) (by simp [c,b,a,kl,hah])
    (by simp [c,b,a,kl,hg,hgh]) (by simp [c,b,a,h0])
    (by simp [c,b,a,h1]) hac
  obtain ⟨d',ed',hd'⟩ := wxexec_sim (WXExec.wm ed) c'' hcc
  have hfinal : c.sets (kernelLocal span 17) []=nativeCleanupState span σ := by
    apply WState.eq
    · funext i
      by_cases hh:i=kernelLocal span 19
      · subst i;simp [c,b,a,nativeCleanupState]
      · simp [c,b,a,nativeCleanupState,Function.update_of_ne hh]
    · rfl
    · rfl
    · rfl
  refine ⟨d',?_,?_⟩
  · exact ((WXExec.wm ea).seq (eb'.seq (ec'.seq ed'))).mono
      (by unfold nativeCleanupCost;omega)
  · simpa only [hfinal] using SimW.trans hd hd'

end NearQuarticWires.StageTuple
