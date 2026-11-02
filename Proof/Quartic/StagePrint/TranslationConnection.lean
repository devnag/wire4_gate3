import Proof.Quartic.StagePrint.TranslationMemory
import Proof.Quartic.Program.Stages
import Proof.Quartic.StagePullback.Canonical

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces

/-- `imp:partition`, paper/paper.tex, and witness (W1): the physical prefix accumulator is exactly the canonical witness partition index. -/
theorem translationNumber_witness (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool) :
    StagePullback.translationNumber (Builder.star c hs) (Builder.translation c hs w)=binaryPrefix w p.k := by
  change (Builder.translationCode (Builder.star c hs) (Builder.translation c hs w)).val=_
  simp only [Builder.translation,Builder.translationEquiv,Equiv.trans_apply,Equiv.apply_symm_apply,
    finCongr_apply,Fin.val_cast,Builder.witness,Algorithm.decodeWitness,Algorithm.witnessBit]
  change binaryPrefix w p.k % 2^p.k=binaryPrefix w p.k
  exact Nat.mod_eq_of_lt (binaryPrefix_lt w p.k)

/-- `sec:params`, witness (W1), and `lem:print`, paper/paper.tex: retaining the finite witness prefix does not alter any of its first k partition bits. -/
theorem binaryPrefix_witnessPrefix (c : Call) (p : Cells.Parameters) (w : List Bool) :
    binaryPrefix (Program.witnessPrefix c p w) p.k=binaryPrefix w p.k := by
  unfold binaryPrefix
  apply Finset.sum_congr rfl
  intro i hi
  have hk : i<Program.witnessReadLength c p := by
    have:=Finset.mem_range.mp hi
    unfold Program.witnessReadLength
    omega
  have hw : (Program.witnessPrefix c p w).getD i false=w.getD i false := by
    simp [Program.witnessPrefix,List.getD,hk,Algorithm.witnessBit]
  rw [hw]

/-- `imp:partition` and `lem:print`, paper/paper.tex: the actually retained finite W1 prefix computes the exact canonical affine translation used by every pulled child. -/
theorem translationNumber_retained (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool) :
    StagePullback.translationNumber (Builder.star c hs) (Builder.translation c hs w)=
      binaryPrefix (Program.witnessPrefix c p w) p.k := by
  rw [binaryPrefix_witnessPrefix,translationNumber_witness]

end NearQuarticWires.StagePrint.Header
