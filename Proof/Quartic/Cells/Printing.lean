import Proof.Quartic.Cells.Children
import Proof.Quartic.Cells.Formulas
import Proof.Wire_3_5.CompilerPrinter

set_option autoImplicit false

namespace NearQuarticWires.Cells
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Compiler
open NearCubicGates.Close.Tabulator

variable {V : ℕ} {ZL ZR : Type}

/-- `lem:print`, paper/paper.tex: one exact stacked equation for each tuple
of disjoint children of a Boolean monomial, retaining its signed integer coefficient. -/
def termOccurrences (kids : Fin V → List (SeparatedEquation ZL ZR)) (H : ℤ)
    (t : Finset (Fin V) × ℤ) : SignedOccurrenceList ZL ZR :=
  (tuples ((t.1.sort (· ≤ ·)).map kids)).map fun es => (t.2, stackEquations H es)

/-- `lem:print`, paper/paper.tex: the literal integer expansion and child substitution. -/
def formulaOccurrences (kids : Fin V → List (SeparatedEquation ZL ZR)) (H : ℤ)
    (F : Formula V) : SignedOccurrenceList ZL ZR := F.expand.flatMap (termOccurrences kids H)

/-- `imp:stack`, paper/paper.tex: bounded integer values justify a single exact stack. -/
theorem stack_indicator (H B : ℤ) (hH : B < H) (es : List (SeparatedEquation ZL ZR))
    (zl : ZL) (zr : ZR) (hB : ∀ e ∈ es, |eqValue e zl zr| ≤ B) :
    bitZ ((stackEquations H es).holds zl zr) = ((es.all fun e => e.holds zl zr).toNat : ℤ) := by
  have hh := stack_holds_iff H B hH es zl zr hB
  have hall : (es.all fun e => e.holds zl zr) = true ↔ ∀ e ∈ es, e.holds zl zr = true :=
    List.all_eq_true
  have he : (stackEquations H es).holds zl zr = (es.all fun e => e.holds zl zr) :=
    Bool.eq_iff_iff.mpr (hh.trans hall.symm)
  rw [he]
  cases es.all (fun e => e.holds zl zr) <;> rfl

/-- `lem:print`, paper/paper.tex: child-tuple expansion preserves each monomial over the integers. -/
theorem termOccurrences_value (kids : Fin V → List (SeparatedEquation ZL ZR))
    (H B : ℤ) (hH : B < H) (t : Finset (Fin V) × ℤ) (zl : ZL) (zr : ZR)
    (β : Fin V → Bool)
    (hk : ∀ i, ((kids i).map fun e => bitZ (e.holds zl zr)).sum = bitZ (β i))
    (hB : ∀ i, ∀ e ∈ kids i, |eqValue e zl zr| ≤ B) :
    (termOccurrences kids H t).value zl zr = t.2 * monomialValue β t.1 := by
  unfold termOccurrences SignedOccurrenceList.value
  rw [List.map_map]
  change ((tuples ((t.1.sort (· ≤ ·)).map kids)).map
    (fun es => t.2 * bitZ ((stackEquations H es).holds zl zr))).sum = _
  have hstack : ∀ es ∈ tuples ((t.1.sort (· ≤ ·)).map kids),
      t.2 * bitZ ((stackEquations H es).holds zl zr) =
        t.2 * ((es.all fun e => e.holds zl zr).toNat : ℤ) := by
    intro es hes
    rw [stack_indicator H B hH es zl zr]
    intro e he
    obtain ⟨L, hL, heL⟩ := mem_tuples_mem _ es hes e he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hL
    exact hB i e heL
  rw [List.map_congr_left hstack, List.sum_map_mul_left, tuples_sum, List.map_map]
  have hkids : ∀ i : Fin V,
      ((kids i).map fun e => ((e.holds zl zr).toNat : ℤ)).sum = ((β i).toNat : ℤ) := by
    intro i
    convert hk i using 1
    · congr 1
      apply List.map_congr_left
      intro e _
      cases e.holds zl zr <;> rfl
    · cases β i <;> rfl
  have hmap : ((fun L : List (SeparatedEquation ZL ZR) =>
      (L.map fun e => ((e.holds zl zr).toNat : ℤ)).sum) ∘ kids) =
      fun i => ((β i).toNat : ℤ) := funext hkids
  rw [hmap, prod_toNat]
  simp only [monomialValue, Finset.mem_sort]

/-- `lem:print`, paper/paper.tex: actual Boolean multilinear expansion equals the signed exact-equation list. -/
theorem formulaOccurrences_value (kids : Fin V → List (SeparatedEquation ZL ZR))
    (H B : ℤ) (hH : B < H) (F : Formula V) (zl : ZL) (zr : ZR) (β : Fin V → Bool)
    (hk : ∀ i, ((kids i).map fun e => bitZ (e.holds zl zr)).sum = bitZ (β i))
    (hB : ∀ i, ∀ e ∈ kids i, |eqValue e zl zr| ≤ B) :
    (formulaOccurrences kids H F).value zl zr = F.eval (boolPoint β) := by
  unfold formulaOccurrences SignedOccurrenceList.value
  rw [listSum_flatMap]
  have ht : ∀ t ∈ F.expand,
      ((termOccurrences kids H t).map fun p => p.1 * bitZ (p.2.holds zl zr)).sum =
        t.2 * monomialValue β t.1 := by
    intro t _
    exact termOccurrences_value kids H B hH t zl zr β hk hB
  rw [List.map_congr_left ht]
  exact Formula.expand_eval β F

/-- `lem:print`, paper/paper.tex: a degree-d monomial yields at most mc^d literal occurrences. -/
theorem termOccurrences_length (kids : Fin V → List (SeparatedEquation ZL ZR)) (H : ℤ)
    (mc : ℕ) (hk : ∀ i, (kids i).length ≤ mc) (t : Finset (Fin V) × ℤ) :
    (termOccurrences kids H t).length ≤ mc ^ t.1.card := by
  unfold termOccurrences
  rw [List.length_map, tuples_length, List.map_map]
  have h := List.prod_le_pow_card ((t.1.sort (· ≤ ·)).map (List.length ∘ kids)) mc (by
    intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact hk i)
  simpa only [List.length_map, Finset.length_sort] using h

/-- `lem:print`, paper/paper.tex: exact distinct-monomial count after integer expansion. -/
theorem formulaOccurrences_length (kids : Fin V → List (SeparatedEquation ZL ZR)) (H : ℤ)
    (mc D : ℕ) (hk : ∀ i, (kids i).length ≤ mc) (F : Formula V) (hD : F.degree ≤ D) :
    (formulaOccurrences kids H F).length ≤ (1 + V * mc) ^ D := by
  unfold formulaOccurrences
  rw [List.length_flatMap]
  calc (F.expand.map fun t => (termOccurrences kids H t).length).sum ≤
      (F.expand.map fun t => mc ^ t.1.card).sum :=
        List.sum_le_sum fun t _ => termOccurrences_length kids H mc hk t
    _ ≤ ∑ d ∈ Finset.range (D + 1), V.choose d * mc ^ d :=
      Terms.sum_card_le D (fun d => mc ^ d) F.expand (Formula.expand_keys_nodup F)
        (fun S hS => (Formula.expand_card_le F S hS).trans hD)
    _ ≤ _ := sum_choose_mul_pow_le V D mc

/-- `lem:print`, paper/paper.tex: concrete atom data; every child and stack is derived from the gate. -/
def compiledFormula {n : ℕ} (B : ℕ) (atoms : Fin V → NormalizedThresholdGate n)
    (coords : Fin V → HalfCoords n ZL ZR) (F : Formula V) : SignedOccurrenceList ZL ZR :=
  formulaOccurrences (fun i => separatedChildren (coords i) (atoms i))
    (((n + 1) * childBound n B : ℕ) + 1) F

/-- `lem:print`, paper/paper.tex: the compiled list evaluates to the actual integer formula on the atoms. -/
theorem compiledFormula_value {n : ℕ} (B : ℕ) (atoms : Fin V → NormalizedThresholdGate n)
    (coords : Fin V → HalfCoords n ZL ZR) (F : Formula V) (hB : ∀ i, GateBits B (atoms i))
    (zl : ZL) (zr : ZR) :
    (compiledFormula B atoms coords F).value zl zr =
      F.eval (boolPoint fun i => (atoms i).eval ((coords i).point zl zr)) := by
  apply formulaOccurrences_value _ _ (((n + 1) * childBound n B : ℕ) : ℤ) (by omega)
  · intro i
    exact separatedChildren_sum _ _ _ _
  · intro i e he
    exact separatedChildren_abs_le _ _ B (hB i) e he zl zr

/-- `lem:print`, paper/paper.tex: the paper's Uocc^D bound for the actual equation list. -/
theorem compiledFormula_length {n : ℕ} (hn : 0 < n) (B D Uocc : ℕ)
    (atoms : Fin V → NormalizedThresholdGate n) (coords : Fin V → HalfCoords n ZL ZR)
    (F : Formula V) (hB : ∀ i, GateBits B (atoms i)) (hD : F.degree ≤ D)
    (hU : 1 + V * childCap n B ≤ Uocc) : (compiledFormula B atoms coords F).length ≤ Uocc ^ D := by
  refine (formulaOccurrences_length _ _ (childCap n B) D ?_ F hD).trans (Nat.pow_le_pow_left hU D)
  intro i
  rw [separatedChildren_length]
  exact exactChildren_length_childCap hn B _ (hB i)

end NearQuarticWires.Cells
