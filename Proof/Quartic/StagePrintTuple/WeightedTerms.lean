import Proof.Quartic.StagePrintTuple.WeightedCensus
import Proof.Gates.Tabulator.Formula

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicGates.Close.Tabulator
open scoped BigOperators

/-- `prop:time`, paper/paper.tex: a physically
serialized list of distinct supports has exactly its finite-set weighted
sum, without a separate maximum term-count multiplier. -/
theorem nodup_list_weight_sum_eq {α : Type} [DecidableEq α] (keys : List α)
    (hn : keys.Nodup) (weight : α → ℕ) :
    (keys.map weight).sum = ∑ S ∈ keys.toFinset, weight S := by
  induction keys with
  | nil => simp
  | cons S keys ih =>
    obtain ⟨hS, ht⟩ := List.nodup_cons.mp hn
    have hs : S ∉ keys.toFinset := by simpa using hS
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons, Finset.sum_insert hs]
    rw [ih ht]

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual distinct serialized support list obeys the
sharp squared original-child census, including empty supports. -/
theorem weighted_support_list_le (V D mc : ℕ) (keys : List (Finset (Fin V)))
    (hn : keys.Nodup) (hD : ∀ S ∈ keys, S.card ≤ D) :
    (keys.map (fun S => mc ^ (2 * S.card))).sum ≤ (1 + V * mc) ^ (2 * D) := by
  rw [nodup_list_weight_sum_eq keys hn]
  apply weighted_squared_child_sum_le
  intro S hS
  exact hD S (List.mem_toFinset.mp hS)

/-- `lem:print` and `prop:time`, paper/paper.tex: exact or modular Terms pay each monomial's own original
child exponent; a maximum term census is never multiplied afterward. -/
theorem weighted_terms_le {V : ℕ} (terms : Terms V) (D mc : ℕ)
    (hn : (Terms.keys terms).Nodup) (hD : ∀ S ∈ Terms.keys terms, S.card ≤ D) :
    (terms.map (fun t => mc ^ (2 * t.1.card))).sum ≤ (1 + V * mc) ^ (2 * D) := by
  simpa only [Terms.keys, List.map_map, Function.comp_def] using
    weighted_support_list_le V D mc (Terms.keys terms) hn hD

end NearQuarticWires.StageTuple
