import Proof.Quartic.StagePrintTuple.PayloadCopy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print` and `prop:time`, paper/paper.tex: a support payload is copied from its actual cursor
after the already parsed support count, preserving both the retained
count prefix and every original variable codec. -/
theorem appendPayloadAtReset_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (bits pre rest : List Bool) (σ : WState ns nr)
    (hs : σ.st src=pre++frame bits++rest) (hsh : σ.sh src=pre.length)
    (hd : σ.sh dst=(σ.st dst).length) (hSC : σ.val SC=0)
    (hcap : σ.val OP+2*bits.length+1≤cap) :
    WExec cap (appendPayloadReset src dst OP SC) σ
      (appendO σ dst OP (marks bits)) (appendPayloadCost bits) := by
  have e1 := pairLoop_spec cap hsd hOS
    (emits_none (cap:=cap) (dst:=dst) (OP:=OP))
    (emits_pair (cap:=cap) (dst:=dst) (OP:=OP)) (false::rest) (by simp)
    bits pre σ
    (by simpa only [NearCubicGates.Close.Codec.frame_eq_marks,
      List.append_assoc,List.singleton_append] using hs)
    (by simpa using hsh) hd
    (by simp only [List.nil_append];change σ.val OP+(marks bits).length≤cap
        simp only [NearCubicGates.Close.Codec.marks_length];omega)
    (by rw [hSC];omega)
  have hcopy : bits.flatMap (fun b=>[]++[true,b])=marks bits := by rfl
  rw [hcopy] at e1
  let τ := adv src dst OP SC σ (marks bits) (2*bits.length)
  have e2 := wrewind_spec cap src SC (2*bits.length) τ
    (by simp [τ,adv,hSC]) (by simp [τ,adv,hSC];omega)
  refine (e1.seq e2).cast cap ?_ (by unfold appendPayloadCost;omega)
  apply WState.eq
  · funext i
    by_cases hi : i=src
    · subst hi
      simp [τ,adv,appendO,hsd,hsh]
    · simp [τ,adv,Function.update_of_ne hi]
  · rfl
  · funext i
    by_cases hi : i=SC
    · subst hi
      simp [τ,adv,appendO,hOS.symm,hSC]
    · simp [τ,adv,Function.update_of_ne hi]
  · rfl

end NearQuarticWires.StageTuple
