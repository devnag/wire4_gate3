import Proof.Quartic.StagePrintTuple.NaturalsReset

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the actual
four-scalar source context is framed once by copying its binary codecs,
without iterating over the sampler radix or walk ordinal values. -/
def contextFrameProgram (P : Fin 2 ↪ Fin (ns+1)) (R : Fin 3 ↪ Fin nr) : WM ns nr :=
  .seq (appendNaturalsReset 4 (P 0) (P 1) (R 0) (R 1) (R 2))
    (.seq (emitC (P 1) (R 0) false) (WM.rewind (P 1) (R 0)))

/-- `lem:print` and `prop:time`, paper/paper.tex: one real source context acquires all physical framing
markers and a reset output head, with its original source preserved. -/
theorem contextFrameProgram_spec (cap : ℕ) (P : Fin 2 ↪ Fin (ns+1)) (R : Fin 3 ↪ Fin nr)
    (values : List ℕ) (hcount : values.length=4) (σ : WState ns nr)
    (hs : σ.st (P 0)=values.flatMap natWord) (hh : σ.sh (P 0)=0)
    (hd : σ.st (P 1)=[]) (hdh : σ.sh (P 1)=0) (hz : ∀i,σ.val (R i)=0)
    (hcap : 2*(values.flatMap natWord).length+2≤cap) :
    WExec cap (contextFrameProgram P R) σ (σ.sets (P 1) (frame (values.flatMap natWord)))
      (1000*((values.flatMap natWord).length+1)) := by
  have e1 := appendNaturalsReset_spec cap (P 0) (P 1) (R 0) (R 1) (R 2)
    (P.injective.ne (by decide)) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) values [] σ (by simpa using hs) hh
    (by rw [hdh,hd];rfl) (hz 1) (hz 2) (by rw [hz 0];omega)
  rw [hcount] at e1
  let a := appendO σ (P 1) (R 0) (marks (values.flatMap natWord))
  have e2 := Codec.emitBit_spec cap (P 1) (R 0) false a
    (by simp [a,appendO,hdh,hd])
    (by simp only [a,appendO_val,Function.update_self,hz,Codec.marks_length];omega)
  let b := appendO a (P 1) (R 0) [false]
  have hb : b=appendO σ (P 1) (R 0) (frame (values.flatMap natWord)) := by
    simp only [b,a,appendO_append,Codec.frame_eq_marks]
  have e3 := wrewind_spec cap (P 1) (R 0) (frame (values.flatMap natWord)).length b
    (by rw [hb];simp [appendO,hz])
    (by rw [hb];simp only [appendO_val,Function.update_self,hz,Nat.zero_add,frame_length];omega)
  refine (e1.seq (e2.seq e3)).cast cap ?_ ?_
  · rw [hb]
    apply WState.eq
    · funext i
      by_cases hi:i=P 1
      · subst i;simp [appendO,hdh]
      · simp [appendO,Function.update_of_ne hi]
    · simp [appendO,hd]
    · funext i
      by_cases hi:i=R 0
      · subst i;simp [appendO,hz]
      · simp [appendO,Function.update_of_ne hi]
    · rfl
  · unfold appendNaturalsCost
    rw [hcount]
    simp only [frame_length]
    omega

end NearQuarticWires.StageTuple
