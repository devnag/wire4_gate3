import Proof.Quartic.StageNativeKids.RoleValid
import Proof.Quartic.StagePrintTuple.RoleInput

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the actual
native request retains its atom as one binary natural codec, which is
copied without enumeration into the real role input. -/
def roleSourceInputProgram (P : Fin 4 ↪ Fin (ns + 1)) (OP SC K : Fin nr) : WM ns nr :=
  .seq (appendPayloadReset (P 0) (P 3) OP SC)
    (.seq (appendNaturalsReset 4 (P 1) (P 3) OP SC K)
      (.seq (appendNaturalsReset 1 (P 2) (P 3) OP SC K)
        (emitC (P 3) OP false)))

/-- `prop:time`, paper/paper.tex: source
assembly charges one finite copy of the header, four context natural
codecs and one actual atom codec, including every source rewind. -/
def roleSourceInputCost (base : List Bool) (context : List ℕ) (atom : ℕ) : ℕ :=
  appendPayloadCost base + appendNaturalsCost context + appendNaturalsCost [atom] + 10

/-- `lem:print` and `prop:time`, paper/paper.tex: the loaded original affine source physically
produces the exact framed role input. All retained source cursors reset;
the radix and walk ordinal are copied in binary. -/
theorem roleSourceInputProgram_spec (cap : ℕ) (P : Fin 4 ↪ Fin (ns + 1))
    (OP SC K : Fin nr) (hOS : OP ≠ SC) (hKO : K ≠ OP) (hKS : K ≠ SC)
    (base : List Bool) (context : List ℕ) (atom : ℕ) (hcount : context.length = 4)
    (restB restC restA : List Bool) (σ : WState ns nr)
    (hb : σ.st (P 0) = frame base ++ restB)
    (hc : σ.st (P 1) = context.flatMap natWord ++ restC)
    (ha : σ.st (P 2) = natWord atom ++ restA)
    (hh : ∀ i : Fin 4, σ.sh (P i) = 0)
    (hd : σ.st (P 3) = []) (ho : σ.val OP = 0)
    (hSC : σ.val SC = 0) (hK : σ.val K = 0)
    (hcap : 2 * (base.length + (context.flatMap natWord).length + (natWord atom).length) + 3 ≤ cap) :
    WExec cap (roleSourceInputProgram P OP SC K) σ
      (appendO σ (P 3) OP (frame (base ++ context.flatMap natWord ++ natWord atom)))
      (roleSourceInputCost base context atom) := by
  have hp {i j : Fin 4} : P i = P j ↔ i = j := P.injective.eq_iff
  have e1 := appendPayloadReset_spec cap (P 0) (P 3) OP SC
    (P.injective.ne (by decide)) hOS base restB σ hb (hh 0)
    (by rw [hh 3, hd]; rfl) hSC (by rw [ho]; omega)
  let s1 := appendO σ (P 3) OP (marks base)
  have e2 := appendNaturalsReset_spec cap (P 1) (P 3) OP SC K
    (P.injective.ne (by decide)) hOS hKO hKS context restC s1
    (by simp [s1, appendO, hp, hc]) (by simp [s1, appendO, hp, hh])
    (by simp [s1, appendO, hh, hd])
    (by simp [s1, appendO, hOS.symm, hSC]) (by simp [s1, appendO, hKO, hK])
    (by simp only [s1, appendO, WState.setv_val, Function.update_self, ho, Codec.marks_length]; omega)
  rw [hcount] at e2
  let s2 := appendO s1 (P 3) OP (marks (context.flatMap natWord))
  have e3 := appendNaturalsReset_spec cap (P 2) (P 3) OP SC K
    (P.injective.ne (by decide)) hOS hKO hKS [atom] restA s2
    (by simpa [s2, s1, appendO, hp] using ha)
    (by simp [s2, s1, appendO, hp, hh])
    (by simp [s2, s1, appendO, hh, hd, List.length_append])
    (by simp [s2, s1, appendO, hOS.symm, hSC])
    (by simp [s2, s1, appendO, hKO, hK])
    (by simp only [s2, s1, appendO, WState.setv_val, Function.update_self, ho,
      Codec.marks_length, List.flatMap_cons, List.flatMap_nil, List.append_nil]; omega)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_cons, List.length_nil] at e3
  let s3 := appendO s2 (P 3) OP (marks (natWord atom))
  have e4 := NearCubicGates.Close.Codec.emitBit_spec cap (P 3) OP false s3
    (by simp [s3, s2, s1, appendO, hh, hd, List.length_append, Nat.add_assoc])
    (by simp only [s3, s2, s1, appendO, WState.setv_val, Function.update_self, ho,
      Codec.marks_length]; omega)
  refine (e1.seq (e2.seq (e3.seq e4))).cast cap ?_ (by
    unfold roleSourceInputCost appendNaturalsCost
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_cons, List.length_nil]
    omega)
  simp only [s3, s2, s1, appendO_append]
  congr 1
  rw [NearCubicGates.Close.Codec.frame_eq_marks]
  simp only [Streaming.marks_append, List.append_assoc]

end NearQuarticWires.StageNativeKids
