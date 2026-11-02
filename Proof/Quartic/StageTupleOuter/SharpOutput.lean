import Proof.Quartic.StagePrintTuple.Request
import Proof.Gates.TabMachine.Stack2

/-!
# The length of the signed equality records

Paper: `lem:print` and `prop:time`, paper/paper.tex.

Every signed record has at most `rowDimension + 2` fields of `2(W+1)+1` bits (`cutRecs_length_le`), and a
monomial with support `S` has at most `mc^|S|` original child tuples when every child pool has at most `mc`
members. The whole record stream is therefore at most `(rowDimension+2)(2W+3)` times the weighted census
`Σ_S mc^(2|S|)  ≤  (1+17G·mc)^(2D)` (`output_length_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.StageTupleOuter

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open StageTuple

theorem stackL_length_le (s : ℕ) (b : ℤ) : ∀ ls : List (List ℤ),(stackL s b ls).length ≤ s+1
  | []=>by simp [stackL]
  | l::ls=>by
    have h:=stackL_length_le s b ls
    simp only [stackL,List.length_zipWith]
    omega

/-- `lem:print`, paper/paper.tex: one signed record has at most `s+2` fields. -/
theorem cutRecs_length_le (Wd s : ℕ) (coef : ℤ) (ls : List (List ℤ)) :
    (cutRecs Wd s coef ls).length ≤ (s+2)*(2*(Wd+1)+1) := by
  unfold cutRecs
  rw [fieldRecs_length]
  unfold cutL
  rw [List.length_append]
  have h:=stackL_length_le s ((magL ls+1 : ℕ) : ℤ) ls
  simp only [List.length_singleton]
  exact Nat.mul_le_mul_right _ (by omega)

theorem prod_lengths_le {α : Type} (mc : ℕ) :
    ∀ Ls : List (List α),(∀L∈Ls,L.length ≤ mc) → (Ls.map List.length).prod ≤ mc^Ls.length
  | [],_=>by simp
  | L::Ls,h=>by
    have h1:=h L (by simp)
    have h2:=prod_lengths_le mc Ls (fun M hM=>h M (by simp [hM]))
    simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ]
    calc
      L.length*(Ls.map List.length).prod ≤ mc*mc^Ls.length := Nat.mul_le_mul h1 h2
      _=_ := by ring

theorem flatMap_length_le {α : Type} (l : List α) (f : α→List Bool) (k : ℕ) (h : ∀x∈l,(f x).length ≤ k) :
    (l.flatMap f).length ≤ l.length*k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1:=h a (by simp)
    have h2:=ih (fun x hx=>h x (by simp [hx]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

/-- `lem:print` and `prop:time`, paper/paper.tex: the signed record
stream is at most a fixed record size times the weighted census. -/
theorem output_length_le (r : TermCutRequest) (mc : ℕ) (hmc : 1 ≤ mc)
    (hkids : ∀i,(r.toRowContext.nativeKids i).length ≤ mc) :
    r.output.length ≤ (r.rowDimension+2)*(2*(r.stackWidth+1)+1)*
      (1+17*(Builder.allGates r.header.call).length*mc)^(2*r.degree) := by
  obtain ⟨R,hR⟩ : ∃R,R=(r.rowDimension+2)*(2*(r.stackWidth+1)+1) := ⟨_,rfl⟩
  have hterm : ∀t∈r.terms,((tuples ((t.1.sort (· ≤ ·)).map r.toRowContext.nativeKids)).flatMap
      (cutRecs r.stackWidth r.rowDimension t.2)).length ≤ R*mc^(2*t.1.card) := by
    intro t _
    have h1:=flatMap_length_le (tuples ((t.1.sort (· ≤ ·)).map r.toRowContext.nativeKids))
      (cutRecs r.stackWidth r.rowDimension t.2) R
      (fun ls _=>by rw [hR];exact cutRecs_length_le _ _ _ _)
    rw [tuples_length] at h1
    have h2:=prod_lengths_le mc ((t.1.sort (· ≤ ·)).map r.toRowContext.nativeKids)
      (fun L hL=>by
        obtain ⟨i,_,rfl⟩:=List.mem_map.mp hL
        exact hkids i)
    simp only [List.length_map,Finset.length_sort] at h2
    have h3 : mc^t.1.card ≤ mc^(2*t.1.card) := Nat.pow_le_pow_right hmc (by omega)
    calc
      _ ≤ (List.map List.length (List.map r.toRowContext.nativeKids (t.1.sort (· ≤ ·)))).prod*R := h1
      _ ≤ mc^(2*t.1.card)*R := Nat.mul_le_mul_right _ (h2.trans h3)
      _=_ := by ring
  have hsum : r.output.length ≤ (r.terms.map fun t=>R*mc^(2*t.1.card)).sum := by
    unfold TermCutRequest.output
    rw [List.length_flatMap]
    exact List.sum_le_sum (fun t ht=>hterm t ht)
  rw [List.sum_map_mul_left] at hsum
  rw [←hR]
  exact hsum.trans (Nat.mul_le_mul_left _ (r.weighted_census mc))

end NearQuarticWires.StageTupleOuter
