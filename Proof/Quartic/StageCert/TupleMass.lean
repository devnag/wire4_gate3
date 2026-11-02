import Proof.Quartic.StageCert.TupleMask

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open scoped BigOperators
open NearCubicGates.Close.Tabulator

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: invalid radix tuples have literal zero mass, so the
executable subset polynomial has exactly the original coefficient mass. -/
theorem tupleElementary_mass {G V : ℕ} (b : Fin G→Formula V) (degree : ℕ) :
    (tupleElementary b degree).mass=
      (Mask.formulaSum (Finset.univ.powersetCard degree) (fun s=>Mask.formulaProd s b)).mass := by
  have hsum : (∑ f : Fin degree→Fin G, if StrictMono f then ∏ i, (b (f i)).mass else 0)=
      ∑ s ∈ (Finset.univ.powersetCard degree : Finset (Finset (Fin G))), ∏ i ∈ s, (b i).mass := by
    have hh := increasingTuple_sum G degree (fun i=>((b i).mass : ℤ))
    exact_mod_cast hh
  simp only [tupleElementary,Mask.formulaListSum_mass,List.map_ofFn,List.sum_ofFn,
    Function.comp_def,tupleTerm,Formula.mass,Mask.formulaListProd_mass,List.map_ofFn,
    List.sum_ofFn,List.prod_ofFn,Mask.formulaSum_mass,Mask.formulaProd_mass]
  have hadd := (tupleAddressEquiv G degree).sum_comp
    (fun f : Fin degree→Fin G=>if StrictMono f then ∏ i, (b (f i)).mass else 0)
  convert hadd.trans hsum using 1
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the actual tuple mask has exactly the original mass bound,
independently of every certification test and atom assignment. -/
theorem tupleMaskFormula_mass {G V : ℕ} (structural : Bool) (b : Fin G→Formula V)
    (tau Xmax : ℕ) :
    (tupleMaskFormula structural b tau Xmax).mass=
      (Mask.maskFormula structural b tau Xmax).mass := by
  unfold tupleMaskFormula Mask.maskFormula
  change (if structural then (1:ℤ) else 0).natAbs*_=(if structural then (1:ℤ) else 0).natAbs*_
  apply congrArg (fun n : ℕ=>(if structural then (1:ℤ) else 0).natAbs*n)
  rw [Mask.formulaListSum_mass,Mask.formulaSum_mass]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def,Formula.mass,tupleElementary_mass]
  exact Fin.sum_univ_eq_sum_range (fun degree : ℕ=>(Mask.newtonCoeff tau degree).natAbs *
    (Mask.formulaSum (Finset.univ.powersetCard degree) (fun s=>Mask.formulaProd s b)).mass) (Xmax+1)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: native coefficient height for the actual tuple source is
polynomial in the original occurrence and population parameters. -/
theorem tupleMaskFormula_mass_le_two_pow {G V : ℕ} (structural : Bool) (b : Fin G→Formula V)
    (tau Xmax : ℕ) (hb : ∀ i, (b i).mass≤16) :
    (tupleMaskFormula structural b tau Xmax).mass≤2^(G+6*Xmax) := by
  rw [tupleMaskFormula_mass]
  simpa only [Fintype.card_fin] using Mask.maskFormula_mass_le_two_pow structural b tau Xmax hb

end NearQuarticWires.StageCert
