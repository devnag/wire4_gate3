import Proof.Quartic.StageMain.MainProgram
import Proof.Quartic.StageMain.MainEntryBounds

/-!
# Discharging the main program's finite capacities

`prop:time`, paper/paper.tex, allows polynomial
binary workspace in the original arity. One common polynomial scale
below pays every actual request and sampler call, while counters for
exponentially many columns are stored in binary and remain within
that same fixed word width.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Bounds

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open Controller Compact

theorem activeCapacity_of_envelope {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ)
    (hb : ∀ r, budget r ≤ K * (r.call.n + 1) ^ d)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p)
    (w : List Bool) (W : ℕ) (hW : 1000000000 * (envelope B1 B2 K d c.n) ^ 2 ≤ W) :
    ActiveCapacity f hd w W W W (100 * W) := by
  let R := envelope B1 B2 K d c.n
  have hpos : 1 ≤ R := envelope_pos B1 B2 K d c.n
  have hpow : R ≤ R ^ 2 := by nlinarith
  have hlinear : 100000 * (R + 1) ≤ W := by change 1000000000 * R ^ 2 ≤ W at hW; nlinarith
  have hquadratic : 30000000 * (R + 1) ^ 2 ≤ W := by
    have hsq : (R + 1) ^ 2 ≤ 4 * R ^ 2 := by nlinarith
    change 1000000000 * R ^ 2 ≤ W at hW
    nlinarith
  have harity : c.n + 1 ≤ R := arity_le B1 B2 K d c.n
  have hell : p.1.ellf ≤ R := (scalar_le K d hd).1
  have hqexp : p.1.Qexp ≤ R := (scalar_le K d hd).2
  have hprefix : (Program.prepWord B1 B2 c w).length ≤ R := compact_le K d hd w
  have hmain : (Program.mainWord B1 B2 c w).length ≤ 400 * R := mainWord_le K d hd w
  have hRW : R < W := by omega
  have hQ : p.1.Q ≤ 2 ^ R := by
    rw [(Cells.prepare_spec _ p.1 p.2).Q_eq]
    exact Nat.pow_le_pow_right (by decide) hqexp
  have hN : 2 ^ (c.n - p.1.k) < 2 ^ W :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have htotal : 2 ^ (c.n - p.1.k) * p.1.Q < 2 ^ W := by
    calc
      _ ≤ 2 ^ R * 2 ^ R := Nat.mul_le_mul
        (Nat.pow_le_pow_right (by decide) (by omega)) hQ
      _ = 2 ^ (2 * R) := by rw [← pow_add]; congr 1; omega
      _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)
  refine {
    widthOk := by omega
    samples := hQ.trans_lt (Nat.pow_lt_pow_right (by decide) hRW)
    compact := (show (Program.prepWord B1 B2 c w).length < W by omega).trans Nat.lt_two_pow_self
    column := ?_
    value := ?_
    samplerInput := by omega
    samplerClock := ?_
    entryInput := ?_
    entryClock := ?_
    stepClock := ?_
    source := ?_
    seed := by omega
    columns := hN
    total := htotal
    output := by omega }
  · intro z
    have hz : natBitLength z.val ≤ R :=
      (NearCubicGates.Close.CounterAsm.nbl_le_of_lt'
        (z.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega : c.n - p.1.k ≤ c.n + 1)))
        (by omega : 1 ≤ c.n + 1)).trans harity
    exact (show natBitLength z.val + 2 < W by omega).trans Nat.lt_two_pow_self
  · intro z j
    have hv := entry_value_bits K d (sampledEntryRequest hd w z j)
    change natBitLength (sampledEntryRequest hd w z j).fieldValue.val ≤ R at hv
    exact (show natBitLength (sampledEntryRequest hd w z j).fieldValue.val + 2 < W by omega).trans
      Nat.lt_two_pow_self
  · exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hell 1) 2)).trans hquadratic
  · intro z j
    have hh := entry_word_le K d (sampledEntryRequest hd w z j)
    change (entryWord (sampledEntryRequest hd w z j)).length ≤ 7 * R at hh
    omega
  · intro z j
    have hh := entry_tagged_budget f K d hb (sampledEntryRequest hd w z j)
    change (sampleTaggedCallee f).bud (.inr (sampledEntryRequest hd w z j)) ≤ 3000 * R at hh
    omega
  · intro z j
    have hz := entry_column_bits K d (sampledEntryRequest hd w z j)
    have hv := entry_value_bits K d (sampledEntryRequest hd w z j)
    change natBitLength z.val ≤ R at hz
    change natBitLength (sampledEntryRequest hd w z j).fieldValue.val ≤ R at hv
    omega
  · rw [← prepWord_eq_compact hd]
    omega

end NearQuarticWires.StageMain.Bounds
