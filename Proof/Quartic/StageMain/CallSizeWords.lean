import Proof.Quartic.Cells.ParametersCallEncoding
import Proof.Gates.Dispatch.Print

/-!
# Length bounds for the normalized call fields

The normalized calls of `thm:counter`, paper/paper.tex,
have bounded integer weights and thresholds and explicit finite tables.
Their literal scalar and list encodings have polynomial length, as
required by the preparation term of `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.CallSize

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces

variable {α : Type}

theorem natWord_le (v : ℕ) : (natWord v).length ≤ 2 * v + 3 := by
  rw [NearCubicGates.Close.Cells.natWord_length]
  have := NearCubicGates.Close.Dispatch.natBitLength_le_succ v
  omega

theorem flatMap_length_le (encode : α → List Bool) (xs : List α) (K : ℕ)
    (h : ∀ x ∈ xs, (encode x).length ≤ K) : (xs.flatMap encode).length ≤ xs.length * K := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      nlinarith

theorem listWord_le (encode : α → List Bool) (xs : List α) (K : ℕ)
    (h : ∀ x ∈ xs, (encode x).length ≤ K) :
    (listWord encode xs).length ≤ 2 * xs.length + 3 + xs.length * K := by
  have hn := natWord_le xs.length
  have ht := flatMap_length_le encode xs K h
  simp only [listWord, List.length_append]
  omega

theorem bitWord_length (bit : Bool) : (bitWord bit).length = 3 := by
  cases bit <;> rfl

theorem intWord_le_bits (z : ℤ) (B : ℕ) (hB : 1 ≤ B) (hz : z.natAbs < 2 ^ B) :
    (intWord z).length ≤ 2 * B + 4 := by
  have hb := NearCubicGates.Close.Dispatch.natBitLength_le_of_lt hz hB
  have hsign : (natWord (if z < 0 then 1 else 0)).length = 3 := by split_ifs <;> rfl
  simp only [intWord, List.length_append, hsign, NearCubicGates.Close.Cells.natWord_length]
  omega

theorem gateWord_le {n : ℕ} (g : NormalizedThresholdGate n) (B : ℕ) (hB : 1 ≤ B)
    (hw : ∀ i, (g.weight i).natAbs < 2 ^ B) (ht : g.threshold.natAbs < 2 ^ B) :
    (gateWord g).length ≤ 2 * n + 3 + (n + 1) * (2 * B + 4) := by
  have hl := listWord_le intWord (List.ofFn g.weight) (2 * B + 4) (by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact intWord_le_bits _ B hB (hw i))
  have hthreshold := intWord_le_bits _ B hB ht
  simp only [List.length_ofFn] at hl
  simp only [gateWord, List.length_append]
  nlinarith

theorem unit_coefficient_word_le {n : ℕ} (C : NCircuit n) (hu : Transfer.UnitTop C) :
    (listWord intWord C.coeffs).length ≤ 8 * C.coeffs.length + 3 := by
  have h := listWord_le intWord C.coeffs 6 (by
    intro z hz
    rw [hu z hz]
    decide)
  omega

theorem gates_le_wires {n : ℕ} (C : NCircuit n) : C.gates.length ≤ Transfer.wires C := by
  unfold Transfer.wires
  induction C.gates with
  | nil => simp
  | cons g gs ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

theorem circuitWord_le {n B : ℕ} (C : NCircuit n) (hw : C.WellFormed B)
    (hu : Transfer.UnitTop C) (hB : 1 ≤ B) :
    (circuitWord C).length ≤ C.gates.length * (2 * n + 3 + (n + 1) * (2 * B + 4) + 20) + 14 := by
  have hg := listWord_le gateWord C.gates (2 * n + 3 + (n + 1) * (2 * B + 4))
    (fun g h => gateWord_le g B hB (hw.2.2.2 g h).1 (hw.2.2.2 g h).2)
  have hc := unit_coefficient_word_le C hu
  have ht := listWord_le bitWord C.table 3 (fun bit _ => (bitWord_length bit).le)
  have heq := Cells.unit_topWeight_eq_occurrences C hw hu
  have htable : C.table.length = 2 * C.gates.length + 1 := hw.2.2.1.trans (by rw [heq])
  rw [← hw.1] at hc
  rw [htable] at ht
  simp only [circuitWord, List.length_append]
  nlinarith

end NearQuarticWires.StageMain.CallSize
