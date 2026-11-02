import Proof.Quartic.StageNativeKids.CounterIndex
import Proof.Quartic.StagePrintTuple.PipelineInput

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: each
real row call is assembled from the retained original occurrence source,
the computed child-loop counter and the retained actual affine header. -/
def pipelineCounterInputProgram (P : Fin 3 ↪ Fin (ns + 1))
    (R : Fin 5 ↪ Fin nr) : WM ns nr :=
  .seq (appendNestedFieldReset (P 0) (P 2) (R 3) (R 4))
    (.seq (copyNestedIndex (R 0) (R 1) (R 2) (P 2) (R 3))
      (.seq (appendNestedFieldReset (P 1) (P 2) (R 3) (R 4))
        (.seq (emitWordM (P 2) (R 3) (List.replicate 8 false))
          (.seq (emitC (P 2) (R 3) false) (WM.rewind (P 2) (R 3))))))

/-- `prop:time`, paper/paper.tex: the
actual row-input clock is linear in both retained sources and the
current original-child index, independently of all walk values. -/
def pipelineCounterInputCost (source header : List Bool) (j : ℕ) : ℕ :=
  2000 * ((frame source).length + (frame header).length + 2 * j + 2)

/-- `lem:print` and `prop:time`, paper/paper.tex: original source, computed loop index and
actual affine metadata physically produce the exact existing eleven-field
pipeline input, with all nested markers, empty fields and rewinds paid. -/
theorem pipelineCounterInputProgram_spec (cap : ℕ) (P : Fin 3 ↪ Fin (ns + 1))
    (R : Fin 5 ↪ Fin nr) (source header : List Bool) (j : ℕ) (σ : WState ns nr)
    (ha : σ.st (P 0) = frame source) (hh : σ.st (P 1) = frame header)
    (hheads : ∀ i, σ.sh (P i) = 0) (hd : σ.st (P 2) = [])
    (hj : σ.val (R 0) = j) (hz : ∀ i, i ≠ 0 → σ.val (R i) = 0)
    (hcap : 4 * ((frame source).length + (frame header).length) + 8 * j + 100 ≤ cap) :
    WExec cap (pipelineCounterInputProgram P R) σ
      (σ.sets (P 2) (frame (pipelineInputWord source (List.replicate j true) header)))
      (pipelineCounterInputCost source header j) := by
  have hp {i k : Fin 3} : P i = P k ↔ i = k := P.injective.eq_iff
  have hr {i k : Fin 5} : R i = R k ↔ i = k := R.injective.eq_iff
  have hcap' := hcap
  simp only [NearCubicWires.RepairOrdinary.frame_length] at hcap'
  have e1 := appendNestedFieldReset_spec cap (P 0) (P 2) (R 3) (R 4)
    (P.injective.ne (by decide)) (R.injective.ne (by decide)) source [] σ
    (by simpa using ha) (hheads 0) (by simp [hheads, hd])
    (hz 4 (by decide)) (by rw [hz 3 (by decide)]; omega)
  let s1 := appendO σ (P 2) (R 3) (marks (frame (frame source)))
  have hj1 : s1.val (R 0) = j := by simp [s1, appendO, hr, hj]
  have e2 := copyNestedIndex_spec cap (R 0) (R 1) (R 2) (P 2) (R 3)
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide)) s1
    (by simp [s1, appendO, hr, hz]) (by simp [s1, appendO, hr, hz])
    (by simp [s1, appendO, hheads, hd]) (by rw [hj1]; omega)
    (by simp [s1, appendO, hr, hz, hj]; omega)
  rw [hj1] at e2
  let s2 := appendO s1 (P 2) (R 3) (marks (frame (frame (List.replicate j true))))
  have e3 := appendNestedFieldReset_spec cap (P 1) (P 2) (R 3) (R 4)
    (P.injective.ne (by decide)) (R.injective.ne (by decide)) header [] s2
    (by simp [s2, s1, appendO, hp, hh]) (by simp [s2, s1, appendO, hp, hheads])
    (by simp [s2, s1, appendO, hheads, hd, List.length_append, Nat.add_assoc])
    (by simp [s2, s1, appendO, hr, hz])
    (by simp [s2, s1, appendO, hz]; omega)
  let s3 := appendO s2 (P 2) (R 3) (marks (frame (frame header)))
  have e4 := emitWordM_spec cap (P 2) (R 3) (List.replicate 8 false) s3
    (by simp [s3, s2, s1, appendO, hheads, hd, List.length_append, Nat.add_assoc])
    (by simp [s3, s2, s1, appendO, hz]; omega)
  let s4 := appendO s3 (P 2) (R 3) (marks (List.replicate 8 false))
  have e5 := Codec.emitBit_spec cap (P 2) (R 3) false s4
    (by simp [s4, s3, s2, s1, appendO, hheads, hd, List.length_append, Nat.add_assoc])
    (by simp [s4, s3, s2, s1, appendO, hz]; omega)
  let s5 := appendO s4 (P 2) (R 3) [false]
  have hs5 : s5 = appendO σ (P 2) (R 3)
      (frame (pipelineInputWord source (List.replicate j true) header)) := by
    simp only [s5, s4, s3, s2, s1, appendO_append, pipelineInputWord_frame, List.append_assoc]
  have e6 := wrewind_spec cap (P 2) (R 3)
    (frame (pipelineInputWord source (List.replicate j true) header)).length s5
    (by rw [hs5]; simp [appendO, hz])
    (by rw [hs5, pipelineInputWord_frame]
        simp [appendO, hz]
        omega)
  refine (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))).cast cap ?_ ?_
  · rw [hs5]
    apply WState.eq
    · funext i
      by_cases hi : i = P 2
      · subst hi; simp [appendO, hheads]
      · simp [appendO, Function.update_of_ne hi]
    · simp [appendO, hd]
    · funext i
      by_cases hi : i = R 3
      · subst hi; simp [appendO, hz]
      · simp [appendO, Function.update_of_ne hi]
    · rfl
  · unfold pipelineCounterInputCost appendNestedFieldCost
    rw [pipelineInputWord_frame]
    simp
    omega

end NearQuarticWires.StageNativeKids
