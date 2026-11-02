import Proof.Quartic.StageGreedyNativeData.Requests
import Proof.Quartic.StageNativeMeaning.Formula
import Proof.Quartic.StageNativeMeaning.Prefix
import Proof.Quartic.StageLift.TargetNormalization

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyNativeData

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Tabulator
open StagePrint StagePrint.NativeMeaning
open scoped BigOperators

theorem cutValue_eq_weakValue (c : MatrixScoreBatch.Cut) (x y : ℕ) :
    StageRecovery.cutValue c x y=EquationRow.weakValue c x y := by
  unfold StageRecovery.cutValue EquationRow.weakValue NearCubicWires.SupplierPrinter.weakCut
  have h : (c.threshold-MatrixScoreBatch.linearForm c.leftWeights x ≤
      MatrixScoreBatch.linearForm c.rightWeights y) ↔
      c.threshold ≤ MatrixScoreBatch.linearForm c.leftWeights x+
        MatrixScoreBatch.linearForm c.rightWeights y := by omega
  simp only [h]

/-- `lem:print`, paper/paper.tex: the global
signed weak table is exactly the sum of the actual per-walk bounded
Terms values at one common original Phi. -/
theorem equalityStream_value {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (high low : Fin (equalityStream r).matrix.U) :
    cutTable (equalityStream r).matrix high low =
      ∑ i : Fin (r.child.cellCall.seed.N^8),
        Terms.eval (actualAtom
          (GreedyEntry.Request.rowContext ⟨r,i⟩) high.val low.val)
          (GreedyEntry.Request.terms ⟨r,i⟩) := by
  rw [StageRecovery.cutTable_eq_sum]
  simp only [cutValue_eq_weakValue,MatrixScoreBatch.Request.phi,(equalityStream r).matrix_columns]
  change ((EquationRow.doubled false (equalityCuts r)).map
    (fun c=>EquationRow.weakValue c
      (MatrixScorePhi.value (PrimT.C4Geo.cols (GreedyCollector.star r)) high.val)
      (MatrixScorePhi.value (PrimT.C4Geo.cols (GreedyCollector.star r)) low.val))).sum=_
  rw [EquationRow.doubled_value]
  simp only [equalityCuts,List.map_flatten,List.map_ofFn,Function.comp_def,List.sum_flatten,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  exact StageNativeMeaning.equalityValue (GreedyEntry.Request.termRequest ⟨r,i⟩) high.val low.val

noncomputable def rawWalkValue {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (i : Fin (r.child.cellCall.seed.N^8)) (z : Fin r.child.cellCall.ncol) : ℤ :=
  let hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  (StageLift.callResidueWalkFormula r.child.call hs r.child.witness
    (StageLift.printWalkAt _ i) r.pattern r.prime r.digits r.residues
    (Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign (StageLift.printWalkAt _ i))).eval
      (boolPoint (Cells.walkAtomPoint (Builder.star r.child.call hs) (by decide : 0<4)
        (callPatterns r.child.call hs (StageLift.printWalkAt _ i)) (callAtoms r.child.call)
        (Builder.center r.child.call hs r.child.witness z)))

/-- `lem:residue` and `lem:print`, paper/paper.tex: summing every original low-first walk
gives the literal printed polynomial, including bad columns. -/
theorem rawWalkValue_sum {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (z : Fin r.child.cellCall.ncol) :
    (∑ i : Fin (r.child.cellCall.seed.N^8),rawWalkValue r i z)=
      Greedy.printedCountOf r.child.cellCall
        (Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign)
        z r.pattern r.prime r.digits r.residues := by
  let f : Cycle.Walk r.child.cellCall.seed.N Algorithm.traceOrder → ℤ := fun walk=>
    Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign walk *
      Walks.walkMaskPoly Algorithm.traceOrder_pos (r.child.cellCall.column z).structural
        (r.child.cellCall.column z).tau (r.child.cellCall.column z).Xmax (r.child.cellCall.column z).X walk *
      NearCubicGates.ResidueCounts.liftedIndicator r.prime r.child.cellCall.e
        (r.child.cellCall.residueForms z r.pattern walk)
        (r.child.cellCall.residueTarget z r.prime r.digits r.residues)
  calc
    _ = ∑ i : Fin (r.child.cellCall.seed.N^8),f (finFunctionFinEquiv.symm i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact StageLift.callResidueWalkFormula_eval r.child.call
        (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) r.child.witness z
        (StageLift.printWalkAt _ i) r.pattern r.prime r.digits r.residues _
    _ = _ := Equiv.sum_comp finFunctionFinEquiv.symm f

/-- `lem:residue` and `lem:print`, paper/paper.tex: actual modular Terms retain the original
raw-index walk value at each original center, with no certification
or bounded-integer-target assumption. -/
theorem terms_center_modEq {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (i : Fin (r.child.cellCall.seed.N^8))
    (high : Fin (2^PrimT.C4Geo.dR (GreedyCollector.star r)))
    (low : Fin (2^PrimT.C4Geo.dRow (GreedyCollector.star r))) :
    Terms.eval (actualAtom
      (GreedyEntry.Request.rowContext ⟨r,i⟩) high.val low.val)
      (GreedyEntry.Request.terms ⟨r,i⟩) ≡
      rawWalkValue r i (centerIndex r.child.call
        (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) low high)
      [ZMOD (r.prime^r.child.selected.1.e : ℕ)] := by
  rw [StageNativeMeaning.actualAtom_centerIndex]
  change Terms.eval _ (StageRecovery.boundedModTerms
    (r.prime^r.child.selected.1.e)
    (StageLift.reduceConstants (r.prime^r.child.selected.1.e) (StageLift.sourceWalkFormula r i))
    (StageLift.residueDegreeBound r.child.selected.1 r.prime)) ≡ _ [ZMOD _]
  apply (StageRecovery.boundedModTerms_eval _ _ _
    (by rw [StageLift.reduceConstants_degree];exact StageLift.sourceWalkFormula_degree r i) _).trans
  exact StageLift.reduced_sourceWalkFormula_eval_modEq_raw r i _

/-- `lem:print`, paper/paper.tex: the entire
coefficient-reduced weak native table is congruent to the literal
original printed count in its original low-first center order. -/
theorem table_center_modEq {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (high : Fin (2^PrimT.C4Geo.dR (GreedyCollector.star r)))
    (low : Fin (2^PrimT.C4Geo.dRow (GreedyCollector.star r))) :
    cutTable (table r).matrix
      (high.castLE (Nat.pow_le_pow_right (by decide)
        (GreedyCollector.star r).centerBits_balanced.1)) low ≡
      Greedy.printedCountOf r.child.cellCall
        (Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign)
        (centerIndex r.child.call (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) low high)
        r.pattern r.prime r.digits r.residues
        [ZMOD (r.prime^r.child.selected.1.e : ℕ)] := by
  apply (show cutTable (table r).matrix _ _ ≡ cutTable (equalityStream r).matrix _ _
    [ZMOD (r.prime^r.child.selected.1.e : ℕ)] from
      StageRecovery.reduceRequest_table_mod _ _ _ le_rfl
        (nativeRequest r).modulus_pos (equalityStream_modulus_fit r) _ _).trans
  rw [equalityStream_value,←rawWalkValue_sum]
  exact Int.ModEq.sum fun i _=>terms_center_modEq r i high low

end NearQuarticWires.StageGreedyNativeData
