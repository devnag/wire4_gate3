import Proof.Quartic.StageLift.PrintRequest

set_option autoImplicit false

namespace NearQuarticWires.StageLift

/-- Step 3 and `lem:print`, paper/paper.tex: the actual dispatched printer has a nonempty original
occurrence pool, since zero-wire calls were already answered directly. -/
theorem print_originalPool_pos {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    0 < (Builder.allGates r.child.call).length := by
  have hwire := (Program.dispatch_admitted r.child.dispatched).2
  by_contra h
  have hz : (Builder.allGates r.child.call).length = 0 := by omega
  have hboth : r.child.call.first.gates.length = 0 ∧ r.child.call.second.gates.length = 0 := by
    simpa only [Builder.allGates, List.length_append, Nat.add_eq_zero_iff] using hz
  have hfirst := List.length_eq_zero_iff.mp hboth.1
  have hsecond := List.length_eq_zero_iff.mp hboth.2
  apply hwire
  simp only [Transfer.callWires, Transfer.wires, hfirst, hsecond, List.map_nil, List.sum_nil,
    Nat.add_zero]

/-- Step 3 and `lem:residue`, paper/paper.tex: the actual original chain endpoint count is the
selected J scalar, including the single endpoint when J=1. -/
theorem print_chain_length {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    r.child.cellCall.J + 1 = r.child.selected.1.J := by
  change r.child.selected.1.J - 1 + 1 = r.child.selected.1.J
  have hJ := (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2).J_pos
  omega

/-- Step 3 and `lem:residue`, paper/paper.tex: the real normalized digit bank contains two selected
J-row blocks, with no hidden endpoint or discarded circuit record. -/
theorem print_digit_count {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (printDigitList r).length = 2 * r.child.selected.1.J := by
  rw [printDigitList_length, print_chain_length]

/-- `lem:residue`, paper/paper.tex: every actual
positive selected exponent makes the digit divisor no larger than q. -/
theorem print_prime_le_modulus {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    r.prime ≤ r.prime ^ r.child.selected.1.e := by
  have hp := (Reconstruct.PrintRequest.prime_prime r).two_le
  have he := (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2).e_pos
  calc
    r.prime = r.prime ^ 1 := by simp
    _ ≤ _ := Nat.pow_le_pow_right (by omega) he

end NearQuarticWires.StageLift
