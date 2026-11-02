import Proof.Quartic.StageMain.MainSizes

/-!
# Lengths of the streams traversed by the main pass

Step 4 of `sec:algorithm`, paper/paper.tex,
traverses one certified-column bitmap and one chosen seed. The finite
preparation prefix and the once-computed modulus are accounted for
separately from that bitmap.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Runtime

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Compact Controller StageLift

theorem compact_lengths (c : Call) (p : Cells.Parameters) (w : List Bool) :
    (callWord c).length ≤ (compactInput c p w).length ∧
    (Program.parametersWord p).length ≤ (compactInput c p w).length ∧
    (preparedPrefixWord c p).length ≤ (compactInput c p w).length ∧
    w.length ≤ (compactInput c p w).length := by
  simp only [compactInput, preparedPrefixWord, List.length_append, List.length_cons, frame_length]
  omega

theorem greedy_length {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    (Program.greedyWord B1 B2 c w).length =
      (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length +
      2 * 2 ^ (c.n - p.1.k) + 16 * p.1.ellf + 5 := by
  rw [greedyWord_compact_layout hd]
  have hs : (Program.runCall c p w).chosenSeed.length = 8 * p.1.ellf :=
    actualChosenSeed_length (Program.runCall c p w)
  have hn : (Program.certifiedBits (Program.runCall c p w)).length = 2 ^ (c.n - p.1.k) := by
    simp only [Program.certifiedBits, List.length_ofFn]
    rfl
  simp only [List.length_append, frame_length, hn, hs]
  have hb : (bitWord (Program.consistentBit (Program.runCall c p w))).length = 3 := by
    cases Program.consistentBit (Program.runCall c p w) <;> rfl
  rw [hb]
  omega

theorem cached_length {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    (cachedMainWord B1 B2 c w).length =
      (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length +
      2 * 2 ^ (c.n - p.1.k) + 17 * p.1.ellf + 5 := by
  simp only [cachedMainWord, List.length_append, greedy_length hd,
    mainFieldBits, mainFieldDegree, hd, binary_length]
  omega

theorem cached_length_le {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) (S : ℕ)
    (hS : 1 ≤ S)
    (hc : (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length ≤ S)
    (he : p.1.ellf ≤ S) :
    (cachedMainWord B1 B2 c w).length ≤ 25 * S * (2 ^ (c.n - p.1.k) * p.1.Q) := by
  have hQ : 1 ≤ p.1.Q := by
    rw [(Cells.prepare_spec _ p.1 p.2).Q_eq]
    exact Nat.one_le_two_pow
  have hN : 1 ≤ 2 ^ (c.n - p.1.k) := Nat.one_le_two_pow
  have hNQ : 2 ^ (c.n - p.1.k) ≤ 2 ^ (c.n - p.1.k) * p.1.Q := Nat.le_mul_of_pos_right _ hQ
  have hSN : 2 ^ (c.n - p.1.k) ≤ S * (2 ^ (c.n - p.1.k) * p.1.Q) :=
    hNQ.trans (Nat.le_mul_of_pos_left _ hS)
  have hSS : S ≤ S * (2 ^ (c.n - p.1.k) * p.1.Q) :=
    Nat.le_mul_of_pos_right _ (by nlinarith)
  rw [cached_length hd]
  nlinarith

end NearQuarticWires.StageMain.Runtime
