import Proof.Wire_3_5.PrimAsmCopyNat
import Proof.Gates.Codec.Emit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a genuine
computed finite counter emits a fixed literal marker block per unit;
this produces unary header fields without an input-list oracle. -/
def repeatLiteral (K : Fin nr) (dst : Fin (ns+1)) (OP : Fin nr)
    (bits : List Bool) : WM ns nr :=
  .whr K (.seq (.dec K) (emitWordM dst OP bits))

/-- `lem:print` and `prop:time`, paper/paper.tex: literal repetition consumes its actual counter and
writes every marker at linear cost in the produced byte length. -/
theorem repeatLiteral_spec (cap : ℕ) (K : Fin nr) (dst : Fin (ns+1)) (OP : Fin nr)
    (hKO : K≠OP) (bits : List Bool) :
    ∀ (j : ℕ) (σ : WState ns nr),σ.val K=j → σ.sh dst=(σ.st dst).length →
      j≤cap → σ.val OP+2*j*bits.length≤cap →
      WExec cap (repeatLiteral K dst OP bits) σ
        ((appendO σ dst OP (marks (List.replicate j bits).flatten)).setv K 0)
        (j*(16*bits.length+4)+1) := by
  intro j
  induction j with
  | zero =>
    intro σ hk _hd _hc _ho
    have hz : σ.setv K 0=σ := by simpa only [hk] using (wsetv_same σ K)
    simpa [repeatLiteral,marks,appendO_nil,hz] using
      (WExec.whrF (cap:=cap) (P:=.seq (.dec K) (emitWordM dst OP bits)) hk)
  | succ j ih =>
    intro σ hk hd hc ho
    have e1 := WExec.dec (cap:=cap) K σ (by omega)
    let d := σ.setv K j
    have e1' : WExec cap (.dec K) σ d 1 := by simpa [d,hk] using e1
    have e2 := emitWordM_spec cap dst OP bits d (by simpa [d] using hd)
      (by simp only [d,WState.setv_val,Function.update_of_ne hKO.symm];nlinarith)
    let e := appendO d dst OP (marks bits)
    have et := ih e
      (by simp [e,d,appendO,hKO])
      (by simp [e,d,appendO,hd])
      (by omega)
      (by simp only [e,appendO_val,Function.update_self,d,WState.setv_val,
          Function.update_of_ne hKO.symm]
          rw [NearCubicGates.Close.Codec.marks_length]
          nlinarith)
    refine (WExec.whrT (by omega) (e1'.seq e2) et).cast cap ?_ (by nlinarith)
    apply WState.eq
    · funext i
      by_cases hi : i=dst
      · subst hi
        simp [e,d,appendO,List.replicate_succ,List.flatten_cons,Streaming.marks_append,
          List.length_append,Nat.add_assoc]
      · simp [e,d,appendO,Function.update_of_ne hi]
    · funext i
      by_cases hi : i=dst
      · subst hi
        simp [e,d,appendO,List.replicate_succ,List.flatten_cons,Streaming.marks_append,List.append_assoc]
      · simp [e,d,appendO,Function.update_of_ne hi]
    · funext i
      by_cases hi : i=K
      · subst hi;simp
      · by_cases hiO : i=OP
        · subst hiO
          simp [e,d,appendO,hKO.symm,List.replicate_succ,List.flatten_cons,
            Streaming.marks_append,List.length_append,Nat.add_assoc]
        · simp [e,d,appendO,Function.update_of_ne hi,Function.update_of_ne hiO]
    · rfl

end NearQuarticWires.StageTuple
