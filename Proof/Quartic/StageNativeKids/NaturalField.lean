import Proof.Quartic.StagePrintTuple.NestedField

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the
actual target-width natural codec is inserted as one framed source
field using its literal bits, without decoding its numeric value. -/
def appendNaturalFieldReset (src dst : Fin (ns + 1)) (OP SC K : Fin nr) : WM ns nr :=
  .seq (CounterAsm.natCopy src SC K (emitDoublePair dst OP))
    (.seq (WM.rewind src SC) (emitPair dst OP false))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual width-codec field, its two
marker layers and field delimiter are physically copied with a linear
binary-source clock, and every source and scratch cursor resets. -/
theorem appendNaturalFieldReset_spec (cap : ℕ) (src dst : Fin (ns + 1)) (OP SC K : Fin nr)
    (hsd : src ≠ dst) (hOS : OP ≠ SC) (hKO : K ≠ OP) (hKS : K ≠ SC)
    (v : ℕ) (rest : List Bool) (σ : WState ns nr)
    (hs : σ.st src = natWord v ++ rest) (hsh : σ.sh src = 0)
    (hd : σ.sh dst = (σ.st dst).length) (hSC : σ.val SC = 0) (hK : σ.val K = 0)
    (hcap : σ.val OP + 4 * (natWord v).length + 3 ≤ cap) :
    WExec cap (appendNaturalFieldReset src dst OP SC K) σ
      (appendO σ dst OP (marks (frame (natWord v)))) (200 * ((natWord v).length + 1)) := by
  have e1 := CounterAsm.natCopy_spec cap hsd hOS hKO hKS
    (emits_doublePair cap dst OP) (d := 4) (by intro b; simp [marks])
    v [] rest σ (by simpa using hs) (by simpa using hsh) hd hK
    (by omega) (by rw [hSC]; omega) (by omega)
  have hm : (natWord v).flatMap (fun b => marks [true, b]) = marks (marks (natWord v)) := by
    simp only [marks, List.flatMap_assoc]
  rw [hm] at e1
  let d := adv src dst OP SC σ (marks (marks (natWord v))) (natWord v).length
  have hlen : (natWord v).length ≤ cap := by omega
  have e2 := wrewind_spec cap src SC (natWord v).length d
    (by simp [d, adv, hSC]) (by simpa [d, adv, hSC] using hlen)
  let e := (d.setv SC 0).seth src (d.sh src - (natWord v).length)
  have eh : e = appendO σ dst OP (marks (marks (natWord v))) := by
    apply WState.eq
    · funext i
      by_cases hi : i = src
      · subst hi; simp [e, d, adv, appendO, hsd, hsh]
      · simp [e, d, adv, Function.update_of_ne hi]
    · rfl
    · funext i
      by_cases hi : i = SC
      · subst hi; simp [e, d, adv, appendO, hOS.symm, hSC]
      · simp [e, d, adv, Function.update_of_ne hi]
    · rfl
  have e3 := emitPair_spec cap dst OP false e
    (by rw [eh]; simp [appendO, hd])
    (by rw [eh]; simp only [appendO_val, Function.update_self, Codec.marks_length]; omega)
  refine (e1.seq (e2.seq e3)).cast cap ?_ (by omega)
  rw [eh, appendO_append]
  congr 1
  simp only [Codec.frame_eq_marks, marks, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

end NearQuarticWires.StageNativeKids
