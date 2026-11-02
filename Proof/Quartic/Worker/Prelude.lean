import Proof.Quartic.Transfer.Counter4

/-!
# The counter of the weak machine for the wire measure

The weak machine of §A.4 (paper/paper.tex) runs the counter of `thm:counter` on its calls. The modules
under `Proof.Quartic.Worker` are adapted from the weak machine of the near-cubic gate proof (`Proof.Gates.Worker`,
`Proof.Gates.WorkerArith`, `Proof.Gates.TermLoop`, `Proof.Gates.Setup`, `Proof.Gates.Codec`), with the counter
`Counter` read as the wire counter `Counter4`. The machine uses the counter's program, its printed intervals, its
running time on normalized and other calls, its witness length and its output format; it never uses completeness.
-/

set_option autoImplicit false

namespace NearQuarticWires.Worker4

open NearCubicGates.Close.Interfaces

/-- The counter run by the weak machine: the wire counter of `thm:counter`. -/
abbrev Counter (B1 B2 : ℕ) : Type := NearQuarticWires.Transfer.Counter4 B1 B2

namespace Counter

/-- Outputs are dyadic with denominator dividing `2^{n+1}`. -/
def DenOK {B1 B2 : ℕ} (ctr : Counter B1 B2) : Prop :=
  ∀ (c : Call) (w : List Bool),
    ((ctr.value c w).1 * 2 ^ (c.n + 1)).den = 1 ∧ ((ctr.value c w).2 * 2 ^ (c.n + 1)).den = 1

/-- Output words have polynomial length. -/
def OutOK {B1 B2 : ℕ} (ctr : Counter B1 B2) : Prop :=
  ∃ C e : ℕ, ∀ (c : Call) (w : List Bool), (outputWord (ctr.value c w)).length ≤ C * (c.n + 1) ^ e

theorem denOK {B1 B2 : ℕ} (ctr : Counter B1 B2) : DenOK ctr := ctr.den

theorem outOK {B1 B2 : ℕ} (ctr : Counter B1 B2) : OutOK ctr := ctr.out

end Counter

end NearQuarticWires.Worker4
