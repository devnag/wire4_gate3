import Proof.Quartic.StagePrintTuple.NaturalsReset
import Proof.Quartic.StagePrintTuple.RoleMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the actual
role input is assembled from the retained affine prefix, four original
context scalars and the selected atom's physical natural-codec word. -/
def roleInputProgram (P : Fin 4 ↪ Fin (ns+1)) (OP SC K : Fin nr) : WM ns nr :=
  .seq (appendPayloadReset (P 0) (P 3) OP SC)
    (.seq (appendNaturalsReset 4 (P 1) (P 3) OP SC K)
      (.seq (appendPayloadReset (P 2) (P 3) OP SC) (emitC (P 3) OP false)))

/-- `prop:time`, paper/paper.tex: each of the
three source pieces is copied once, with all source rewinds charged. -/
def roleInputCost (base atom : List Bool) (context : List ℕ) : ℕ :=
  appendPayloadCost base + appendNaturalsCost context + appendPayloadCost atom + 10

/-- `lem:print` and `prop:time`, paper/paper.tex: the real role source packet is built with all framing
markers and its delimiter. Every retained input cursor is reset, and
the four context values are copied as bytes without unary decoding. -/
theorem roleInputProgram_spec (cap : ℕ) (P : Fin 4 ↪ Fin (ns+1)) (OP SC K : Fin nr)
    (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC)
    (base atom : List Bool) (context : List ℕ) (hcount : context.length=4)
    (restB restC restA : List Bool) (σ : WState ns nr)
    (hb : σ.st (P 0)=frame base++restB)
    (hc : σ.st (P 1)=context.flatMap natWord++restC)
    (ha : σ.st (P 2)=frame atom++restA)
    (hh : ∀ i : Fin 4,σ.sh (P i)=0)
    (hd : σ.st (P 3)=[]) (ho : σ.val OP=0)
    (hSC : σ.val SC=0) (hK : σ.val K=0)
    (hcap : 2*(base.length+(context.flatMap natWord).length+atom.length)+3≤cap) :
    WExec cap (roleInputProgram P OP SC K) σ
      (appendO σ (P 3) OP (frame (base++context.flatMap natWord++atom)))
      (roleInputCost base atom context) := by
  have hp {i j : Fin 4} : P i=P j ↔ i=j := P.injective.eq_iff
  have e1 := appendPayloadReset_spec cap (P 0) (P 3) OP SC
    (P.injective.ne (by decide)) hOS base restB σ hb (hh 0)
    (by rw [hh 3,hd];rfl) hSC (by rw [ho];omega)
  let s1 := appendO σ (P 3) OP (marks base)
  have e2 := appendNaturalsReset_spec cap (P 1) (P 3) OP SC K
    (P.injective.ne (by decide)) hOS hKO hKS context restC s1
    (by simp [s1,appendO,hp,hc]) (by simp [s1,appendO,hp,hh])
    (by simp [s1,appendO,hp,hh,hd])
    (by simp [s1,appendO,hOS.symm,hSC]) (by simp [s1,appendO,hKO,hK])
    (by simp only [s1,appendO,WState.setv_val,Function.update_self,ho,Codec.marks_length];omega)
  rw [hcount] at e2
  let s2 := appendO s1 (P 3) OP (marks (context.flatMap natWord))
  have e3 := appendPayloadReset_spec cap (P 2) (P 3) OP SC
    (P.injective.ne (by decide)) hOS atom restA s2
    (by simp [s2,s1,appendO,hp,ha]) (by simp [s2,s1,appendO,hp,hh])
    (by simp [s2,s1,appendO,hp,hh,hd,List.length_append])
    (by simp [s2,s1,appendO,hOS.symm,hSC])
    (by simp only [s2,s1,appendO,WState.setv_val,Function.update_self,ho,Codec.marks_length];omega)
  let s3 := appendO s2 (P 3) OP (marks atom)
  have e4 := NearCubicGates.Close.Codec.emitBit_spec cap (P 3) OP false s3
    (by simp [s3,s2,s1,appendO,hp,hh,hd,List.length_append,Nat.add_assoc])
    (by simp only [s3,s2,s1,appendO,WState.setv_val,Function.update_self,ho,Codec.marks_length];omega)
  refine (e1.seq (e2.seq (e3.seq e4))).cast cap ?_ (by unfold roleInputCost;omega)
  simp only [s3,s2,s1,appendO_append]
  congr 1
  rw [NearCubicGates.Close.Codec.frame_eq_marks]
  simp only [Streaming.marks_append,List.append_assoc]

end NearQuarticWires.StageTuple
