import Proof.Quartic.StagePrep.PrefixPhysical
import Proof.Quartic.Cells.ParametersCallEncoding
import Proof.Gates.Dispatch.Main

/-!
# Polynomial length and physical cost of the witness prefix

Paper: the witness in paper/paper.tex and
`prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces

/-- The witness prefix in `sec:algorithm`, paper/paper.tex has
polynomial length in the original call arity. -/
theorem witnessReadLength_preparation_bound (c : Call) (p : Cells.Parameters)
    (hs : Cells.ParameterRules (Builder.callInput c) p) :
    Program.witnessReadLength c p ≤ 5 * (c.n + 1) ^ 5 := by
  have hk : p.k ≤ c.n := hs.k_lt_n.le
  have hl : p.lambda ≤ c.n :=
    Cells.CoreRules.lambda_le_n (hs : Cells.CoreRules (Builder.callInput c) p)
  have hm : p.mu ≤ c.n := hs.mu_le_lambda.trans hl
  have hj : p.J + 1 ≤ 2 * (c.n + 1) := by
    have hjb := hs.J_bound
    rw [hs.Jmax_eq] at hjb
    omega
  have hG : Builder.occurrences c 0 + Builder.occurrences c 1 ≤ 2 * c.n ^ 4 := by
    have hg := hs.input_valid.2.2.1.trans hs.input_valid.2.2.2.1
    simpa [Builder.callInput, Builder.occurrences, Builder.gatesOf] using hg
  have hG' : Builder.occurrences c 0 + Builder.occurrences c 1 ≤ 2 * (c.n + 1) ^ 4 :=
    hG.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) _))
  have hprod := Nat.mul_le_mul hj hG'
  have hprod' : (p.J + 1) * (Builder.occurrences c 0 + Builder.occurrences c 1) ≤
      4 * (c.n + 1) ^ 5 := by
    calc
      _ ≤ (2 * (c.n + 1)) * (2 * (c.n + 1) ^ 4) := hprod
      _ = _ := by ring
  have hn : c.n ≤ (c.n + 1) ^ 5 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by norm_num) _)
  unfold Program.witnessReadLength
  omega

/-- The dispatched witness prefix of `sec:algorithm`, paper/paper.tex is bounded by the original call-word length. -/
theorem witnessReadLength_callWord_bound {B1 B2 : ℕ} {c : Call}
    {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p) :
    Program.witnessReadLength c p.1 ≤ 5 * ((callWord c).length + 1) ^ 5 := by
  have hn := Cells.dispatched_n_le_callWord hd
  have hs := Cells.prepare_spec _ p.1 p.2
  exact (witnessReadLength_preparation_bound c p.1 hs).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hn _) _))

/-- The physical prefix-read work in `prop:time`, paper/paper.tex, excludes the length of the witness suffix. -/
noncomputable def prefixCost (B1 B2 K : ℕ) (c : Call) (_ : List Bool) : ℕ :=
  match Program.dispatch B1 B2 c with
  | none => 0
  | some p => (10 * Program.witnessReadLength c p.1 + 6) * KC (wdOf K (callWord c).length)

/-- The physical prefix work of `prop:time`, paper/paper.tex, satisfies the original-call polynomial budget. -/
theorem prefixCost_poly (B1 B2 K : ℕ) : Program.PolyCost (prefixCost B1 B2 K) := by
  have hp : PolyB (fun L => (10 * (5 * (L + 1) ^ 5) + 6) * KC (wdOf K L)) := by
    unfold KC wdOf
    polyb
  obtain ⟨C, e, hCe⟩ := hp
  refine ⟨C, e, ?_⟩
  intro c w
  unfold prefixCost
  cases hd : Program.dispatch B1 B2 c with
  | none => simp
  | some p =>
    exact (Nat.mul_le_mul_right _ (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (witnessReadLength_callWord_bound hd)) _)).trans (hCe _)

end NearQuarticWires.StagePrep
