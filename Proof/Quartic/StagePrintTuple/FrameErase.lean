import Proof.Quartic.StagePrintTuple.CacheErase

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a genuine
finite framed cache is scanned once to count its actual cells, then
erased backwards by that count with no capacity-sized sweep. -/
def eraseFrameCache (src : Fin (ns+1)) (SC : Fin nr) : WM ns nr :=
  .seq (CounterAsm.frameCopy src SC (fun _=>WM.skip)) (eraseCacheBackward src SC)

/-- `lem:print` and `prop:time`, paper/paper.tex: actual framed-cache erasure restores a reusable blank
cache and zero cursor/scratch, with linear cost in the scanned bytes. -/
theorem eraseFrameCache_spec (cap : ℕ) (src dummy : Fin (ns+1)) (SC OP : Fin nr)
    (hsd : src≠dummy) (hOS : OP≠SC) (bits : List Bool) (σ : WState ns nr)
    (hs : σ.st src=frame bits) (hh : σ.sh src=0)
    (hd : σ.sh dummy=(σ.st dummy).length) (ho : σ.val OP≤cap) (hSC : σ.val SC=0)
    (hcap : (frame bits).length≤cap) :
    ∃τ,WExec cap (eraseFrameCache src SC) σ τ (60*((frame bits).length+1)) ∧
      SimW (σ.sets src []) τ := by
  have e1 := CounterAsm.frameCopy_spec cap hsd hOS
    (emits_none (cap:=cap) (dst:=dummy) (OP:=OP)) (d:=0) (by intro b;simp)
    bits [] [] σ (by simpa using hs) (by simpa using hh) hd
    (by simpa using ho) (by rw [hSC];omega)
  have hz : (frame bits).flatMap (fun _=>([]:List Bool))=[] := by simp
  rw [hz] at e1
  let a := adv src dummy OP SC σ [] (frame bits).length
  have e2 := eraseCacheBackward_spec cap src SC (frame bits) [] a
    (by simp [a,adv,appendO,hs])
    (by simp [a,adv,hh]) (by simp [a,adv,hSC]) hcap
  let b := ((a.sets src (List.replicate (frame bits).length false++[])).seth src 0).setv SC 0
  have he : b=σ.sets src (List.replicate (frame bits).length false) := by
    apply WState.eq
    · funext i
      by_cases hi:i=src
      · subst i;simp [b,a,adv,appendO,hh]
      · simp [b,a,adv,appendO,Function.update_of_ne hi]
    · simp [b,a,adv,appendO]
    · funext i
      by_cases hi:i=SC
      · subst i;simp [b,a,adv,appendO,hOS.symm,hSC]
      · simp [b,a,adv,appendO,Function.update_of_ne hi]
    · rfl
  refine ⟨b,(e1.seq e2).mono (by omega),?_⟩
  rw [he]
  refine ⟨rfl,rfl,rfl,?_⟩
  intro i
  by_cases hi:i=src
  · subst i
    simpa only [WState.sets_st,Function.update_self] using
      (rdEq_blank (List.replicate (frame bits).length false) (by simp)).symm
  · simp only [WState.sets_st,Function.update_of_ne hi]
    exact RdEq.refl _

end NearQuarticWires.StageTuple
