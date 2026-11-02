import Proof.Quartic.StageLift.SourceEnvelope
import Proof.Quartic.StageLift.FormulaBytes
import Proof.Quartic.StageRecovery.ResidueFactor

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open scoped BigOperators

/-- `cor:conditional`, `lem:residue` and `sec:params`,
paper/paper.tex:
each actual signed Gamma input is smaller than the selected prime
power, before the requested positive/negative split is made. -/
theorem print_gamma_natAbs_lt_modulus {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (walk : Cycle.Walk r.child.cellCall.seed.N 4) :
    (r.child.cellCall.walkWeight r.child.seedPrefix walk).natAbs <
      r.prime ^ r.child.selected.1.e := by
  let hs := Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  have hu := Builder.usesParameters r.child.call hs r.child.witness
  have hg := r.child.cellCall.guard_of_parameters (Builder.algorithmParameters r.child.call hs)
    hu.N_eq hu.Q_eq hu.S_eq hu.primes_eq hu.e_eq r.prime r.prime_mem
    r.child.seedPrefix r.child.prefix_le
  have hsingle : |r.child.cellCall.walkWeight r.child.seedPrefix walk| ≤
      ∑ w, |r.child.cellCall.walkWeight r.child.seedPrefix w| :=
    Finset.single_le_sum (f := fun w => |r.child.cellCall.walkWeight r.child.seedPrefix w|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ walk)
  have hnonneg : (0 : ℤ) ≤ ∑ w, |r.child.cellCall.walkWeight r.child.seedPrefix w| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hcast : ((r.child.cellCall.walkWeight r.child.seedPrefix walk).natAbs : ℤ) <
      ((r.prime ^ r.child.selected.1.e : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs, Nat.cast_pow]
    change |r.child.cellCall.walkWeight r.child.seedPrefix walk| < (r.prime : ℤ) ^ r.child.cellCall.e
    omega
  exact_mod_cast hcast

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the actual retained Gamma integer needs
only polynomial source width, regardless of its table's length. -/
theorem print_gamma_binary_width {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (walk : Cycle.Walk r.child.cellCall.seed.N 4) :
    natBitLength (r.child.cellCall.walkWeight r.child.seedPrefix walk).natAbs + 2 ≤
      (sourceEnvelope r + 1) ^ 2 + 2 := by
  have hb := sourceEnvelope_bounds r
  have hg := codec_nbl_mono (print_gamma_natAbs_lt_modulus r walk).le
  have hq := StageRecovery.primePower_bits_envelope r.prime r.child.selected.1.e
    (sourceEnvelope r) hb.prime hb.exponent
  omega

end NearQuarticWires.StageLift
