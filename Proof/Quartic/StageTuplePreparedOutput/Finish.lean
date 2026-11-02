import Proof.Quartic.StageTuplePreparedOutput.Data

set_option autoImplicit false

namespace NearQuarticWires.StageTuplePreparedOutput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: retained
suffix caches are followed by the actual empty last field, outer-frame
delimiter and rewind using the physically accumulated output counter. -/
def finishProgram (instructions : List (Fin (ns+1)×Bool)) (dst : Fin (ns+1))
    (OP SC : Fin nr) : WM ns nr :=
  .seq (cachesProgram instructions dst OP SC)
    (.seq (emitPair dst OP false) (.seq (emitC dst OP false) (WM.rewind dst OP)))

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact finite suffix, last empty
field and whole-frame delimiter are physically emitted, then all heads
and registers are restored through the real measured output counter. -/
theorem finishProgram_spec (cap : ℕ) (dst : Fin (ns+1)) (OP SC : Fin nr) (hOS : OP≠SC)
    (fields : List (CacheField ns)) (pre : List Bool) (σ : WState ns nr)
    (hsrc : ∀ f∈fields, f.source≠dst ∧ σ.st f.source=frame f.bits ∧ σ.sh f.source=0)
    (hd : σ.st dst=[]) (hh : σ.sh dst=0) (hOP : σ.val OP=0) (hSC : σ.val SC=0)
    (hcap : pre.length+cachesReserve fields+10≤cap) :
    WExec cap (finishProgram (fields.map CacheField.instruction) dst OP SC)
      (appendO σ dst OP pre)
      (σ.sets dst (pre++fields.flatMap CacheField.bytes++[true,false,false]))
      (cachesClock fields+100+10*(pre.length+cachesReserve fields+1)) := by
  let a := appendO σ dst OP pre
  have ha : ∀ f∈fields, f.source≠dst ∧ a.st f.source=frame f.bits ∧ a.sh f.source=0 := by
    intro f hf
    obtain ⟨hfd, hfs, hfh⟩ := hsrc f hf
    exact ⟨hfd, by simp [a, appendO, hfd, hfs], by simp [a, appendO, hfd, hfh]⟩
  have ec := cachesProgram_spec cap dst OP SC hOS fields a ha
    (by simp [a, appendO, hd, hh]) (by simp [a, appendO, hOS.symm, hSC])
    (by simp only [a, appendO_val, Function.update_self, hOP, Nat.zero_add]; omega)
  let b := appendO a dst OP (fields.flatMap CacheField.bytes)
  have hb : b.val OP=pre.length+(fields.flatMap CacheField.bytes).length := by
    simp [b, a, appendO, hOP]
  have hbytes := cachesBytes_le fields
  have ee := emitPair_spec cap dst OP false b
    (by simp [b, a, appendO, hd, hh]) (by rw [hb]; omega)
  let c := appendO b dst OP [true,false]
  have hc : c.val OP=pre.length+(fields.flatMap CacheField.bytes).length+2 := by
    simp only [c, appendO_val, Function.update_self, hb, List.length_cons, List.length_nil]
  have ef := emitC_spec cap dst OP false c
    (by simp [c, b, a, appendO, hd, hh, Nat.add_assoc]) (by rw [hc]; omega)
  let d := appendO c dst OP [false]
  let bytes := pre++fields.flatMap CacheField.bytes++[true,false,false]
  have hdop : d.val OP=bytes.length := by
    simp only [d, appendO_val, Function.update_self, hc, bytes, List.length_append,
      List.length_cons, List.length_nil]
  have er := wrewind_spec cap dst OP bytes.length d hdop (by
    rw [hdop]
    simp only [bytes, List.length_append, List.length_cons, List.length_nil]
    omega)
  refine (ec.seq (ee.seq (ef.seq er))).cast cap ?_ ?_
  · have hdeq : d=appendO σ dst OP bytes := by
      simp only [d, c, b, a, appendO_append, bytes, List.append_assoc]
      rfl
    rw [hdeq]
    apply WState.eq
    · funext i
      by_cases hi : i=dst
      · subst i; simp [appendO, hh]
      · simp [appendO, hi]
    · simp [appendO, hd, bytes, List.append_assoc]
    · funext i
      by_cases hi : i=OP
      · subst i; simp [hOP]
      · simp [appendO, hi]
    · rfl
  · simp only [bytes, List.length_append, List.length_cons, List.length_nil]
    omega

end NearQuarticWires.StageTuplePreparedOutput
