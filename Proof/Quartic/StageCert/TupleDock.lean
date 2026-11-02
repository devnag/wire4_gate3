import Proof.Quartic.StageCert.TupleStream
import Proof.Quartic.StageCert.SubsetTuples

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open scoped BigOperators
open NearCubicGates.Close.CounterMachine.CellTablesProg
open NearCubicWires.RepairRepresentation

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: reversal converts arithmetic most-significant-first tuple
digits into the unchanged finite-function coordinate order. -/
def reverseTuple (G a : ℕ) : (Fin a→Fin G) ≃ (Fin a→Fin G) where
  toFun f i := f i.rev
  invFun f i := f i.rev
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the exact tuple-address bijection uses no padded labels. -/
def tupleAddressEquiv (G a : ℕ) : Fin (G^a) ≃ (Fin a→Fin G) :=
  finFunctionFinEquiv.symm.trans (reverseTuple G a)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: each physical digit is literally its tuple coordinate. -/
theorem tupleAddress_digit (G a : ℕ) (address : Fin (G^a)) (i : Fin a) :
    (tupleAddressEquiv G a address i).val=address.val/G^(a-1-i.val)%G := by
  change address.val/G^(a-(i.val+1))%G=_
  rw [show a-(i.val+1)=a-1-i.val by omega]

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the emitted block equals the exact bounded tuple. -/
theorem tupleAddress_words (G a : ℕ) (address : Fin (G^a)) :
    digs G address.val a=List.ofFn (fun i=>(tupleAddressEquiv G a address i).val) := by
  apply List.ext_getElem
  · simp [digs]
  · intro i hi hj
    simp only [digs,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rw [tupleAddress_digit]

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: summing the guarded arithmetic tuple enumeration gives
the complete original subset polynomial on every integer assignment. -/
theorem addressedTupleSum_eval {G V a : ℕ} (b : Fin G→NearCubicGates.Close.Tabulator.Formula V)
    (point : Fin V→ℤ) :
    (∑ address : Fin (G^a), (tupleTerm b (tupleAddressEquiv G a address)).eval point)=
      (Mask.formulaSum (Finset.univ.powersetCard a) (fun s=>Mask.formulaProd s b)).eval point := by
  rw [(tupleAddressEquiv G a).sum_comp (fun f=>(tupleTerm b f).eval point)]
  exact tupleSum_eval b point

end NearQuarticWires.StageCert
