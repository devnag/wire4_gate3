import Proof.Quartic.StageCert.FormulaTokenCounts
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open scoped BigOperators
open NearCubicGates.Close.Tabulator

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: strictly increasing bounded tuples enumerate each original
occurrence subset exactly once, with its full integer product. -/
theorem increasingTuple_sum (G a : ℕ) (b : Fin G→ℤ) :
    (∑ f : Fin a→Fin G, if StrictMono f then ∏ i, b (f i) else 0) =
      ∑ s ∈ (Finset.univ.powersetCard a : Finset (Finset (Fin G))), ∏ i ∈ s, b i := by
  classical
  rw [←Finset.sum_filter]
  refine Finset.sum_bij (fun f _=>Finset.univ.image f) ?_ ?_ ?_ ?_
  · intro f hf
    have hm := (Finset.mem_filter.mp hf).2
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _,by rw [Finset.card_image_of_injective _ hm.injective]; simp⟩
  · intro f hf g hg he
    have fm := (Finset.mem_filter.mp hf).2
    have gm := (Finset.mem_filter.mp hg).2
    have hc : (Finset.univ.image f).card=a := by
      rw [Finset.card_image_of_injective _ fm.injective]
      simp
    have ff := Finset.orderEmbOfFin_unique hc (fun i=>Finset.mem_image.mpr ⟨i,by simp,rfl⟩) fm
    have gg := Finset.orderEmbOfFin_unique hc
      (fun i=>by rw [he]; exact Finset.mem_image.mpr ⟨i,by simp,rfl⟩) gm
    exact ff.trans gg.symm
  · intro s hs
    have hc := (Finset.mem_powersetCard.mp hs).2
    refine ⟨s.orderEmbOfFin hc,Finset.mem_filter.mpr ⟨by simp,(s.orderEmbOfFin hc).strictMono⟩,?_⟩
    exact Finset.image_orderEmbOfFin_univ s hc
  · intro f hf
    have hm := (Finset.mem_filter.mp hf).2
    exact (Finset.prod_image (fun _ _ _ _ he=>hm.injective he)).symm

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the executable tuple summand uses a literal zero coefficient
on every unordered or repeated tuple, retaining all valid subset products. -/
def tupleTerm {G V a : ℕ} (b : Fin G→Formula V) (f : Fin a→Fin G) : Formula V :=
  .mul (.const (if StrictMono f then 1 else 0))
    (Mask.formulaListProd (List.ofFn (fun i=>b (f i))))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: tuple guards act as exact integer coefficients on every
assignment; no passing-population or Boolean-mask premise is used. -/
theorem tupleTerm_eval {G V a : ℕ} (b : Fin G→Formula V) (f : Fin a→Fin G)
    (point : Fin V→ℤ) :
    (tupleTerm b f).eval point = if StrictMono f then ∏ i, (b (f i)).eval point else 0 := by
  simp only [tupleTerm,Formula.eval,Mask.formulaListProd_eval,List.map_ofFn,List.prod_ofFn]
  split <;> simp

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: bounded tuple enumeration has the same exact integer value
as the original powerset-cardinality formula, including all bad columns. -/
theorem tupleSum_eval {G V a : ℕ} (b : Fin G→Formula V) (point : Fin V→ℤ) :
    (∑ f : Fin a→Fin G, (tupleTerm b f).eval point) =
      (Mask.formulaSum (Finset.univ.powersetCard a) (fun s=>Mask.formulaProd s b)).eval point := by
  simp only [tupleTerm_eval,Mask.formulaSum_eval,Mask.formulaProd_eval]
  exact increasingTuple_sum G a (fun i=>(b i).eval point)

end NearQuarticWires.StageCert
