import Proof.Quartic.StageMain.MainEnvelope
import Proof.Quartic.StageMain.SampleTaggedData

/-!
# Polynomial requests and calls for sampled entries

Step 4 of `sec:algorithm`, paper/paper.tex,
constructs one request from the retained finite prefix and two binary
indices. The exact tagged ordinary call charges that finite request,
the two-bit answer and the supplier's arity-polynomial running time.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Bounds

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

theorem entry_column_bits {B1 B2 : ℕ} (K d : ℕ) (r : EntryRequest B1 B2) :
    natBitLength r.column.val ≤ envelope B1 B2 K d r.call.n := by
  have hc : r.column.val < 2 ^ (r.call.n + 1) := r.column.isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hb := NearCubicGates.Close.CounterAsm.nbl_le_of_lt' hc (by omega : 1 ≤ r.call.n + 1)
  exact hb.trans (arity_le B1 B2 K d r.call.n)

theorem entry_value_bits {B1 B2 : ℕ} (K d : ℕ) (r : EntryRequest B1 B2) :
    natBitLength r.fieldValue.val ≤ envelope B1 B2 K d r.call.n := by
  have hs := Cells.prepare_spec _ r.selected.1 r.selected.2
  have hpos : 1 ≤ r.selected.1.ellf := hs.seedParameters.one_le_ell
  have hb := NearCubicGates.Close.CounterAsm.nbl_le_of_lt' r.fieldValue.isLt hpos
  exact hb.trans (scalar_le K d r.dispatched).1

theorem entry_word_le {B1 B2 : ℕ} (K d : ℕ) (r : EntryRequest B1 B2) :
    (entryWord r).length ≤ 7 * envelope B1 B2 K d r.call.n := by
  have hc := compact_le K d r.dispatched r.witness
  have hz := entry_column_bits K d r
  have hv := entry_value_bits K d r
  have hp := envelope_pos B1 B2 K d r.call.n
  simp only [entryWord, List.length_append, NearCubicGates.Close.Cells.natWord_length]
  omega

theorem entry_tagged_budget {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ)
    (hb : ∀ r, budget r ≤ K * (r.call.n + 1) ^ d) (r : EntryRequest B1 B2) :
    (sampleTaggedCallee f).bud (.inr r) ≤ 3000 * envelope B1 B2 K d r.call.n := by
  have hw := entry_word_le K d r
  have ht := (hb r).trans (entry_budget_le B1 B2 K d r.call.n)
  have hp := envelope_pos B1 B2 K d r.call.n
  change 200 * ((entryWord r).length + 2 + budget r + 1) + 12 ≤ _
  omega

end NearQuarticWires.StageMain.Bounds
