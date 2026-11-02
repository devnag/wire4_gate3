import Proof.Quartic.Program.Output

/-!
# The closed exits of preparation

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Interfaces

/-- The successful dispatch of `sec:params`, paper/paper.tex, carries exactly the original call, complete
parameter record and bounded witness prefix. -/
theorem prepWord_of_dispatch {B1 B2 : ℕ} (c : Call) (w : List Bool)
    (p : Program.Selected c) (hd : Program.dispatch B1 B2 c = some p) :
    Program.prepWord B1 B2 c w = true :: (callWord c ++
      Program.parametersWord p.1 ++ NearCubicWires.RepairOrdinary.frame
        (Program.witnessPrefix c p.1 w)) := by
  unfold Program.prepWord Program.stageWord
  rw [hd]

/-- A nonnormalized call uses the literal default exit of
`sec:params`, paper/paper.tex. -/
theorem prepWord_of_not_admitted {B1 B2 : ℕ} (c : Call) (w : List Bool)
    (h : ¬ Transfer.Admitted4 B1 B2 c) :
    Program.prepWord B1 B2 c w = false :: outputWord Algorithm.soundDefault := by
  unfold Program.prepWord Program.stageWord
  rw [Program.dispatch_of_not_admitted h]
  rw [Program.admittedValue_of_not_admitted Builder.value h]

/-- A zero-wire call uses its exact closed value in
`sec:params`, paper/paper.tex. -/
theorem prepWord_of_zero {B1 B2 : ℕ} (c : Call) (w : List Bool)
    (ha : Transfer.Admitted4 B1 B2 c) (hw : Transfer.callWires c = 0) :
    Program.prepWord B1 B2 c w = false :: outputWord (Builder.closedValue c) := by
  classical
  have hn : ¬ c.n < 4 := by have h := ha.1; omega
  have hd : Program.dispatch B1 B2 c = none := by
    unfold Program.dispatch
    simp only [hw, ne_eq, not_true_eq_false, and_false, if_false]
  unfold Program.prepWord Program.stageWord
  rw [hd, Program.admittedValue_of_admitted Builder.value ha]
  unfold Builder.value
  rw [if_pos (Builder.Shaped.of_admitted ha), if_neg hn, if_pos hw]

/-- A failed public parameter computation uses the literal
default of `sec:params`, paper/paper.tex. -/
theorem prepWord_of_prepare_none {B1 B2 : ℕ} (c : Call) (w : List Bool)
    (ha : Transfer.Admitted4 B1 B2 c) (hw : Transfer.callWires c ≠ 0)
    (hp : Cells.prepare (Builder.callInput c) = none) :
    Program.prepWord B1 B2 c w = false :: outputWord Algorithm.soundDefault := by
  classical
  have hn : ¬ c.n < 4 := by have h := ha.1; omega
  have hd : Program.dispatch B1 B2 c = none := by
    unfold Program.dispatch
    rw [if_pos (show Transfer.Admitted4 B1 B2 c ∧ Transfer.callWires c ≠ 0 from ⟨ha, hw⟩)]
    split <;> simp_all
  have hv : Builder.value c w = Algorithm.soundDefault := by
    unfold Builder.value
    rw [if_pos (Builder.Shaped.of_admitted ha), if_neg hn, if_neg hw]
    split <;> simp_all
  unfold Program.prepWord Program.stageWord
  rw [hd, Program.admittedValue_of_admitted Builder.value ha]
  simp only [hv]

end NearQuarticWires.StagePrep
