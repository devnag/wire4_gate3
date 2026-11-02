import Proof.Quartic.StageCert.TupleDock

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open scoped BigOperators
open NearCubicGates.Close.Tabulator

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the executable elementary-symmetric formula visits exact
radix addresses and suppresses repeated or unordered occurrence tuples. -/
def tupleElementary {G V : ℕ} (b : Fin G→Formula V) (degree : ℕ) : Formula V :=
  Mask.formulaListSum (List.ofFn (fun address : Fin (G^degree)=>
    tupleTerm b (tupleAddressEquiv G degree address)))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: tuple addressing preserves the complete original integer
elementary-symmetric polynomial on every input assignment. -/
theorem tupleElementary_eval {G V : ℕ} (b : Fin G→Formula V) (degree : ℕ)
    (point : Fin V→ℤ) :
    (tupleElementary b degree).eval point=
      (Mask.formulaSum (Finset.univ.powersetCard degree) (fun s=>Mask.formulaProd s b)).eval point := by
  simp only [tupleElementary,Mask.formulaListSum_eval,List.map_ofFn,List.sum_ofFn]
  exact addressedTupleSum_eval b point

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: tuple-mask source uses original integer Newton constants,
the unchanged original atom pool, and no certificate-dependent simplification. -/
def tupleMaskFormula {G V : ℕ} (structural : Bool) (b : Fin G→Formula V)
    (tau Xmax : ℕ) : Formula V :=
  .mul (.const (if structural then 1 else 0))
    (Mask.formulaListSum (List.ofFn (fun degree : Fin (Xmax+1)=>
      Formula.mul (.const (Mask.newtonCoeff tau degree.val)) (tupleElementary b degree.val))))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the executable radix mask equals the literal powerset mask
also on bad columns, arbitrary integer atom assignments, and every witness. -/
theorem tupleMaskFormula_eval {G V : ℕ} (structural : Bool) (b : Fin G→Formula V)
    (tau Xmax : ℕ) (point : Fin V→ℤ) :
    (tupleMaskFormula structural b tau Xmax).eval point=
      (Mask.maskFormula structural b tau Xmax).eval point := by
  unfold tupleMaskFormula Mask.maskFormula
  change (if structural then (1:ℤ) else 0)*_=(if structural then (1:ℤ) else 0)*_
  apply congrArg (fun z : ℤ=>(if structural then (1:ℤ) else 0)*z)
  rw [Mask.formulaListSum_eval,Mask.formulaSum_eval]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def,Formula.eval]
  simp_rw [tupleElementary_eval]
  exact Fin.sum_univ_eq_sum_range (fun degree : ℕ=>Mask.newtonCoeff tau degree *
    (Mask.formulaSum (Finset.univ.powersetCard degree) (fun s=>Mask.formulaProd s b)).eval point)
    (Xmax+1)

/-- `lem:print`(c), paper/paper.tex: each guarded
tuple has exactly its original occurrence-product degree bound. -/
theorem tupleTerm_degree_le {G V a : ℕ} (b : Fin G→Formula V)
    (f : Fin a→Fin G) (hb : ∀ i, (b i).degree≤2) :
    (tupleTerm b f).degree≤2*a := by
  simp only [tupleTerm,Formula.degree,zero_add,Mask.formulaListProd_degree,
    List.map_ofFn,List.sum_ofFn]
  calc
    _≤∑ _i : Fin a,2 := Finset.sum_le_sum (fun i _=>hb (f i))
    _=2*a := by simp [Nat.mul_comm]

/-- `lem:print`(c), paper/paper.tex: the exact
tuple source preserves the paper's quadratic-per-population degree. -/
theorem tupleElementary_degree_le {G V : ℕ} (b : Fin G→Formula V)
    (degree : ℕ) (hb : ∀ i, (b i).degree≤2) :
    (tupleElementary b degree).degree≤2*degree := by
  apply Mask.formulaListSum_degree_le
  intro f hf
  obtain ⟨address,rfl⟩ := List.mem_ofFn.mp hf
  exact tupleTerm_degree_le b (tupleAddressEquiv G degree address) hb

/-- `lem:print`(c), paper/paper.tex: replacing
powerset order by actual radix enumeration introduces no degree loss. -/
theorem tupleMaskFormula_degree_le {G V : ℕ} (structural : Bool) (b : Fin G→Formula V)
    (tau Xmax : ℕ) (hb : ∀ i, (b i).degree≤2) :
    (tupleMaskFormula structural b tau Xmax).degree≤2*Xmax := by
  change 0+_≤_
  rw [zero_add]
  apply Mask.formulaListSum_degree_le
  intro f hf
  obtain ⟨degree,rfl⟩ := List.mem_ofFn.mp hf
  change 0+_≤_
  rw [zero_add]
  exact (tupleElementary_degree_le b degree.val hb).trans (Nat.mul_le_mul_left _ (by omega))

end NearQuarticWires.StageCert
