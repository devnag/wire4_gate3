import Proof.Quartic.StageRecovery.TableCongruence
import Proof.Quartic.StageRecovery.PacketMachine
import Proof.Quartic.StagePrint.FullTable

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms.SInt

/-- `lem:print`, paper/paper.tex: reducing coefficients
makes every weighted native dominance contribution nonnegative. -/
theorem reduceCut_nonneg (modulus : ℕ) (hm : 0 < modulus)
    (c : MatrixScoreBatch.Cut) : 0 ≤ (reduceCut modulus c).coefficient := by
  exact Int.emod_nonneg _ (by exact_mod_cast (ne_of_gt hm))

/-- `lem:print`, paper/paper.tex: every actual table
entry is nonnegative when all its physical cut coefficients are. -/
theorem cutTable_nonneg (r : MatrixScoreBatch.Request)
    (h : ∀ c ∈ r.cuts, 0 ≤ c.coefficient) (i j : Fin r.U) :
    0 ≤ StagePrint.cutTable r i j := by
  rw [cutTable_eq_sum]
  apply List.sum_nonneg
  intro value hv
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
  exact mul_nonneg (h c hc) (Int.natCast_nonneg _)

/-- `lem:print`, paper/paper.tex: a nonnegative native
table has its literal row-major natural entries, with no signed cast loss. -/
def tableNaturals (r : StagePrint.TableRequest) : List ℕ :=
  (pvals false (StagePrint.cutTable r.matrix)).map Int.toNat

/-- `lem:print`, paper/paper.tex: every integer appearing
in the row-major native table is an actual table entry. -/
theorem mem_pvals_false {u : ℕ} (f : Fin u → Fin u → ℤ) (value : ℤ)
    (hv : value ∈ pvals false f) : ∃ i j, f i j = value := by
  change value ∈ (List.ofFn fun i => List.ofFn fun j => f i j).flatten at hv
  obtain ⟨row, hrow, hv⟩ := List.mem_flatten.mp hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hv
  exact ⟨i, j, hj⟩

/-- `lem:print`, paper/paper.tex: the exact row-major
natural table retains the complete table count. -/
theorem tableNaturals_length (r : StagePrint.TableRequest) :
    (tableNaturals r).length = r.count := by
  simp only [tableNaturals, List.length_map, pvals, Bool.false_eq_true, if_false,
    StagePrint.TableRequest.count, List.length_flatten, List.map_ofFn, Function.comp_def,
    List.length_ofFn, List.sum_ofFn]
  simp

/-- `lem:print`, paper/paper.tex: actual native bounds
produce the strict decoder record bound at the same native bit width. -/
theorem tableNaturals_fit (r : StagePrint.TableRequest)
    (h : ∀ c ∈ r.matrix.cuts, 0 ≤ c.coefficient) :
    ∀ value ∈ tableNaturals r, 2 * value < 2 ^ (r.q + 1) := by
  intro value hv
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
  obtain ⟨i, j, rfl⟩ := mem_pvals_false _ z hz
  have hnonneg := cutTable_nonneg r.matrix h i j
  have hb := r.value_bound i j
  have hab : (StagePrint.cutTable r.matrix i j).toNat =
      (StagePrint.cutTable r.matrix i j).natAbs := by
    exact_mod_cast ((Int.toNat_of_nonneg hnonneg).trans (Int.natAbs_of_nonneg hnonneg).symm)
  rw [hab]
  have hpow : 2 ^ (r.q - 1) ≤ 2 ^ r.q := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  rw [Nat.pow_succ]
  omega

/-- `lem:print`, paper/paper.tex: the actual nonnegative
native table and recovery modulus determine the bounded packet request. -/
def tablePacket (r : StagePrint.TableRequest) (modulus : ℕ) (hm : 0 < modulus)
    (h : ∀ c ∈ r.matrix.cuts, 0 ≤ c.coefficient) : PacketRequest where
  width := r.q + 1
  modulus := modulus
  values := tableNaturals r
  modulus_pos := hm
  values_fit := tableNaturals_fit r h

/-- `lem:print`, paper/paper.tex: the native packet
itself is exactly the decoder's record suffix, preserving every entry. -/
theorem tablePacket_stream (r : StagePrint.TableRequest) (modulus : ℕ) (hm : 0 < modulus)
    (h : ∀ c ∈ r.matrix.cuts, 0 ≤ c.coefficient) :
    packetStream (tablePacket r modulus hm h).width (tablePacket r modulus hm h).values =
      r.output := by
  unfold packetStream tablePacket tableNaturals StagePrint.TableRequest.output
  rw [List.map_map]
  apply congrArg NearCubicGates.Close.WordPrograms.recStream
  apply List.map_congr_left
  intro z hz
  obtain ⟨i, j, rfl⟩ := mem_pvals_false _ z hz
  have hn := cutTable_nonneg r.matrix h i j
  have he : encS (StagePrint.cutTable r.matrix i j) =
      2 * (StagePrint.cutTable r.matrix i j).toNat := by
    have ha : (StagePrint.cutTable r.matrix i j).toNat =
        (StagePrint.cutTable r.matrix i j).natAbs := by
      exact_mod_cast ((Int.toNat_of_nonneg hn).trans (Int.natAbs_of_nonneg hn).symm)
    rw [encS, if_neg (not_lt.mpr hn), Nat.add_zero, ha]
  change SignedSortKey.binary (r.q + 1) (2 * (StagePrint.cutTable r.matrix i j).toNat) = _
  rw [he]

end NearQuarticWires.StageRecovery
