import Proof.Quartic.Cells.AsymptoticsCap
import Proof.Quartic.Builder.Complete

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-- `def:class` and `sec:counting`, paper/paper.tex: every occurrence contributes at least its top wire. -/
theorem occurrences_le_wires {n : ℕ} (C : NCircuit n) : C.gates.length ≤ Transfer.wires C := by
  unfold Transfer.wires
  induction C.gates with
  | nil => simp
  | cons g gs ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- `sec:counting` and `sec:params`, paper/paper.tex: every admitted call of positive wire count supplies the
complete admission predicate of the canonical parameter computation. -/
theorem callInput_valid {B1 B2 : ℕ} (c : Call)
    (hadm : Transfer.Admitted4 B1 B2 c) (hW : Transfer.callWires c ≠ 0) :
    ParameterArithmetic.ValidInput (Builder.callInput c) := by
  rcases hadm with ⟨hn, _, _, _, _, hempty, _, _, hwire, hbeta, hsmall, _, _⟩
  have hpos : 0 < c.radius := by
    by_contra h
    have hnonpos : c.radius ≤ 0 := le_of_not_gt h
    have hprod : c.radius * (c.n : ℚ) ^ B1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos (by positivity)
    linarith
  have hG : c.first.gates.length + c.second.gates.length ≤ Transfer.callWires c :=
    Nat.add_le_add (occurrences_le_wires c.first) (occurrences_le_wires c.second)
  refine ⟨hn, Nat.pos_of_ne_zero hW, hG, hwire, hpos, hsmall, ?_⟩
  intro hp
  have hpair : c.kind ≠ .pair := by
    intro heq
    change decide (c.kind = .pair) = false at hp
    simp only [heq, decide_true, Bool.true_eq_false] at hp
  change c.second.gates.length = 0
  rw [hempty hpair]
  rfl

/-- The exact `QuarticCap` obligation of `thm:counter`,
paper/paper.tex: the canonically computed parameters of
every admitted call satisfy all completeness side conditions under one
positive constant times `beta A4(n)`, for every call kind. -/
theorem builder_quarticCap (B1 B2 : ℕ) : Builder.QuarticCap B1 B2 := by
  obtain ⟨a, ha, onset, _, hcap⟩ := eventual_quartic_cap B1
  refine ⟨a, ha, onset, ?_⟩
  intro c hn hadm hW0 hW
  have hv := callInput_valid c hadm hW0
  have hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1 := hadm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨p, hp, _, hk, hX, hw⟩ := hcap (Builder.callInput c) hn hv hb hW
  exact ⟨p, hp, ⟨hk, hX, hw⟩⟩

end NearQuarticWires.Cells
