import Proof.Quartic.StagePrint.NativeEquations
import Proof.Quartic.StagePrintTuple.WeightedTerms

set_option autoImplicit false

namespace NearQuarticWires.StagePrint

open NearCubicWires NearCubicWires.ThresholdCompiler
open NearCubicGates.Close.Tabulator
open scoped BigOperators

/-- `lem:print` and `prop:time`, paper/paper.tex: a tuple uses one actual original child per chosen
variable, with no separate maximum-child multiplication. -/
theorem native_tuple_count_le (r : StageTuple.RowContext) (mc : ℕ)
    (hkids : ∀ i,(r.nativeKids i).length ≤ mc)
    (indices : List (Fin (17*(Builder.allGates r.header.call).length))) :
    (tuples (indices.map (nativeKidsEquations r))).length ≤ mc^indices.length := by
  rw [tuples_length,List.map_map]
  induction indices with
  | nil=>simp
  | cons i indices ih=>
      simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ]
      have hi : (nativeKidsEquations r i).length ≤ mc := by
        have he:=congrArg List.length (nativeKidsEquations_fields r i)
        simp only [List.length_map] at he
        exact he.trans_le (hkids i)
      calc (nativeKidsEquations r i).length *
          (indices.map ((List.length) ∘ nativeKidsEquations r)).prod ≤ mc*mc^indices.length:=Nat.mul_le_mul hi ih
        _=mc^indices.length*mc:=Nat.mul_comm _ _

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual full equality count of one Formula has
the first-moment support bound before taking any square. -/
theorem nativeEqualityCuts_count_le (r : StageTuple.TermCutRequest) (mc : ℕ)
    (hkids : ∀ i,(r.toRowContext.nativeKids i).length ≤ mc) :
    (nativeEqualityCuts r).length≤(1+17*(Builder.allGates r.header.call).length*mc)^r.degree := by
  have hterms : (nativeEqualityCuts r).length≤(r.terms.map (fun t=>mc^t.1.card)).sum := by
    unfold nativeEqualityCuts
    simp only [List.length_flatMap,List.length_map]
    have bound : ∀ ts : Terms (17*(Builder.allGates r.header.call).length),
        (ts.map (fun t=>(tuples ((t.1.sort (· ≤ ·)).map (nativeKidsEquations r.toRowContext))).length)).sum ≤
          (ts.map (fun t=>mc^t.1.card)).sum := by
      intro ts
      induction ts with
      | nil=>simp
      | cons t ts ih=>
          simp only [List.map_cons,List.sum_cons]
          apply Nat.add_le_add _ ih
          simpa only [Finset.length_sort] using native_tuple_count_le r.toRowContext mc hkids (t.1.sort (· ≤ ·))
    exact bound r.terms
  apply hterms.trans
  have he : (r.terms.map (fun t=>mc^t.1.card)).sum=
      ((Terms.keys r.terms).map (fun S=>mc^S.card)).sum := by
    simp only [Terms.keys,List.map_map,Function.comp_def]
  rw [he,StageTuple.nodup_list_weight_sum_eq _ r.terms_nodup]
  apply StageTuple.weighted_support_sum_le
  intro S hS
  exact r.terms_degree S (List.mem_toFinset.mp hS)

/-- `lem:print` and `prop:time`, paper/paper.tex: quadratic per-walk equality-header work obeys the
literal exponent2D, including zero Terms and empty supports. -/
theorem nativeEqualityCuts_square_le (r : StageTuple.TermCutRequest) (mc : ℕ)
    (hkids : ∀ i,(r.toRowContext.nativeKids i).length ≤ mc) :
    (nativeEqualityCuts r).length^2≤(1+17*(Builder.allGates r.header.call).length*mc)^(2*r.degree) := by
  have h:=Nat.pow_le_pow_left (nativeEqualityCuts_count_le r mc hkids) 2
  simpa only [←pow_mul,Nat.mul_comm r.degree 2] using h

end NearQuarticWires.StagePrint
