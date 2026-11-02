import Proof.Quartic.Greedy.Loop
import Proof.Quartic.Greedy.Cost
import Proof.Gates.Cells.OutLen

/-!
# The `greedy` stage of the counter program

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

The `greedy` field of `Program.MachineComponents` is a word function from `certWord` to `frame greedyWord` whose
cost is a ledger cost. It is assembled here from

* the control of the `S` rounds (`SeedLoop`), which works for every integer objective;
* one child evaluation (`child`): a word function computing `intWord Ψ̃(π)` (`childObjective`) from `childInput`,
  with a ledger cost.

The word computed by the rounds on the child objective is `frame greedyWord` (`greedyWord_eq_seedSuffix`), and the
cost `K (S + 1)(childBound + |certWord| + S + 1)` is a ledger cost because `S = O(n)` (`seedRounds_le`) and the
length of `certWord` is a ledger cost (`CertSize`). The second fact follows from any word
function writing `frame certWord` with a ledger cost (`certSize_of_cert`), in particular from the `cert` stage.
-/

set_option autoImplicit false

namespace NearQuarticWires.Greedy

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- A word function computes every output equal to its own. -/
def wordFunctionOfOutputEq {Request : Type} {input output output' : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (h : ∀ r, output r = output' r) :
    WordFunction Request input output' budget where
  program := f.program
  realizes r := by
    obtain ⟨receipt, hrun, hout⟩ := f.realizes r
    exact ⟨receipt, hrun, hout.trans (h r)⟩

/-- A cost below a ledger cost is a ledger cost. -/
theorem LedgerCost.mono {f g : Call → List Bool → ℕ} (hfg : ∀ c w, f c w ≤ g c w) (hg : LedgerCost B1 B2 g) :
    LedgerCost B1 B2 f := by
  obtain ⟨K, e, h⟩ := hg
  exact ⟨K, e, fun c w => (hfg c w).trans (h c w)⟩

/-! ## The facts about sizes -/

/-- **`S = O(k + λ)`** (`prop:time`): on every call, the number of rounds of Step 3 is at most
`8 (2B₁ + 103)(n + 1)`. On a dispatched call `S = 2m ℓ_f = 8 max(k, Q_exp + 1)` (`sec:params`), with `k < n` and
`Q_exp ≤ 3k/4 + (2B₁ + 100) λ` (`lem:asymptotics`, `Cells.ParameterRules.Qexp_upper`) and `λ = ⌈lg n⌉ ≤ n`. -/
theorem seedRounds_le (c : Call) : seedRounds B1 B2 c ≤ 8 * (2 * B1 + 103) * (c.n + 1) := by
  unfold seedRounds
  split
  · rename_i p hp
    have hadm := (dispatch_admitted hp).1
    have hs := Cells.prepare_spec _ p.1 p.2
    have hb : 1 ≤ (Builder.callInput c).beta * ((Builder.callInput c).n : ℚ) ^ B1 := hadm.2.2.2.2.2.2.2.2.2.1
    have hQ := Cells.ParameterRules.Qexp_upper hs B1 hb
    have hk : p.1.k < c.n := Cells.ParameterRules.k_lt_n hs
    have hlam : p.1.lambda ≤ c.n := by
      rw [hs.lambda_eq]
      exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
    have hS : p.1.S = 2 * p.1.m * p.1.ellf := hs.S_eq
    rw [hS, hs.m_eq, hs.ellf_eq]
    set T := (2 * B1 + 100) * c.n with hT
    have hTl : (2 * B1 + 100) * p.1.lambda ≤ T := Nat.mul_le_mul_left _ hlam
    have hdiv : 3 * p.1.k / 4 ≤ p.1.k := by omega
    have key : max p.1.k (p.1.Qexp + 1) ≤ T + 2 * c.n + 1 := by
      apply max_le <;> omega
    calc 2 * 4 * max p.1.k (p.1.Qexp + 1) ≤ 8 * (T + 2 * c.n + 1) := by omega
      _ ≤ 8 * (2 * B1 + 103) * (c.n + 1) := by rw [hT]; nlinarith
  · exact Nat.zero_le _

/-- `prop:time`: the word after Step 2 has the length of a ledger cost (its certified-column bits
are `2^{n-k}` bits, everything else is polynomial). -/
def CertSize (B1 B2 : ℕ) : Prop := LedgerCost B1 B2 fun c w => (certWord B1 B2 c w).length

/-- The length of the word after Step 2 is bounded by the cost of any word function writing it. In particular the
`cert` stage of `Program.MachineComponents` gives `CertSize`. -/
theorem certSize_of_cert {certBudget : Call → List Bool → ℕ}
    (cert : WordFunction (Call × List Bool) (fun r => prepWord B1 B2 r.1 r.2)
      (fun r => frame (certWord B1 B2 r.1 r.2)) (fun r => certBudget r.1 r.2))
    (hcost : LedgerCost B1 B2 certBudget) : CertSize B1 B2 := by
  obtain ⟨K, e, h⟩ := hcost
  refine ⟨K + 1, e, fun c w => ?_⟩
  have h1 := NearCubicGates.Close.Cells.wf_out_len cert (c, w)
  rw [frame_length] at h1
  have h2 := h c w
  have h3 : 1 ≤ ((callWord c).length + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  dsimp only at h1 ⊢
  nlinarith

/-! ## The components -/

/-- **The components of the `greedy` stage** (Step 3, paper/paper.tex):

* `loop`: the control of the `S` rounds, for every integer objective;
* `child`: one child evaluation, computing `intWord Ψ̃(π)` (`childObjective`, paper/paper.tex) from the word
  after Step 2 and the framed prefix `π`, within `childBudget`;
* `childBound`, `childBound_spec`, `childCost`: a bound on the cost of the child evaluations of a call, which is a
  ledger cost (`prop:time`: each child computes `|W_s|` coefficients, prints at most
  `4^m |𝒫| P^{2J+2}` tables and solves at most `2^{n-k} 4^m P^{2J}` exact systems). -/
structure GreedyComponents (B1 B2 : ℕ) where
  /-- The control of the `S` rounds. -/
  loop : SeedLoop B1 B2
  /-- The cost of one child evaluation. -/
  childBudget : ChildRequest B1 B2 → ℕ
  /-- One child evaluation: `Ψ̃(π)` as an integer word. -/
  child : WordFunction (ChildRequest B1 B2) childInput
    (fun q => NearCubicGates.Close.Interfaces.intWord (childObjective q)) childBudget
  /-- A bound on the cost of the child evaluations of a call. -/
  childBound : Call → List Bool → ℕ
  childBound_spec : ∀ q : ChildRequest B1 B2, childBudget q ≤ childBound q.call q.witness
  /-- The child evaluations of a call cost a ledger cost. -/
  childCost : LedgerCost B1 B2 childBound

namespace GreedyComponents

variable (G : GreedyComponents B1 B2)

/-- The cost of the `greedy` stage: `K (S + 1)(childBound + |certWord| + S + 1)`. -/
noncomputable def budget (c : Call) (w : List Bool) : ℕ :=
  G.loop.K * (seedRounds B1 B2 c + 1) * (G.childBound c w + (certWord B1 B2 c w).length + seedRounds B1 B2 c + 1)

/-- **The `greedy` stage** (Step 3, `sec:algorithm`, paper/paper.tex): the `S` rounds on the child objective map
the word after Step 2 to the framed word after Step 3. -/
noncomputable def stage : WordFunction (Call × List Bool) (fun r => certWord B1 B2 r.1 r.2)
    (fun r => frame (greedyWord B1 B2 r.1 r.2)) (fun r => G.budget r.1 r.2) :=
  wordFunctionOfOutputEq (G.loop.program childObjective G.childBudget G.childBound G.child G.childBound_spec)
    (fun r => by rw [greedyWord_eq_seedSuffix])

/-- **The cost of the `greedy` stage is a ledger cost** (`prop:time`). -/
theorem budget_cost (hC : CertSize B1 B2) : LedgerCost B1 B2 G.budget := by
  set A := 8 * (2 * B1 + 103) + 1 with hA
  have hround0 : ∀ c, dispatch B1 B2 c = none → seedRounds B1 B2 c = 0 := by
    intro c h
    unfold seedRounds
    rw [h]
  have hround1 : ∀ c, seedRounds B1 B2 c + 1 ≤ A * (c.n + 1) ^ 1 := by
    intro c
    have := seedRounds_le (B1 := B1) (B2 := B2) c
    rw [pow_one, hA]
    nlinarith
  have hS1 : LedgerCost B1 B2 fun c (_ : List Bool) => (seedRounds B1 B2 c + 1) * 1 :=
    LedgerCost.mul_dispatched A 1 (fun c _ h => by rw [hround0 c h]; omega) (fun c _ _ _ => hround1 c)
      (LedgerCost.of_poly ⟨1, 0, fun _ _ => by simp⟩)
  have hg : LedgerCost B1 B2 fun c w =>
      (G.childBound c w + (certWord B1 B2 c w).length) + (seedRounds B1 B2 c + 1) * 1 :=
    LedgerCost.add (LedgerCost.add G.childCost hC) hS1
  have hf := LedgerCost.mul_dispatched (B1 := B1) (B2 := B2)
    (f := fun c (_ : List Bool) => G.loop.K * (seedRounds B1 B2 c + 1)) (G.loop.K * A) 1
    (fun c _ h => by rw [hround0 c h]; nlinarith)
    (fun c _ _ _ => by
      have := hround1 c
      calc G.loop.K * (seedRounds B1 B2 c + 1) ≤ G.loop.K * (A * (c.n + 1) ^ 1) := Nat.mul_le_mul_left _ this
        _ = G.loop.K * A * (c.n + 1) ^ 1 := by ring) hg
  refine LedgerCost.mono (fun c w => le_of_eq ?_) hf
  unfold budget
  ring

end GreedyComponents

/-- **The `greedy` field of `Program.MachineComponents`** (Step 3, paper/paper.tex, with the cost of
`prop:time`): from the components of the stage and the fact `CertSize`, a word function from `certWord` to
`frame greedyWord` whose cost is a ledger cost. -/
theorem greedy_of_components (G : GreedyComponents B1 B2) (hC : CertSize B1 B2) :
    ∃ greedyBudget : Call → List Bool → ℕ,
      Nonempty (WordFunction (Call × List Bool) (fun r => certWord B1 B2 r.1 r.2)
        (fun r => frame (greedyWord B1 B2 r.1 r.2)) (fun r => greedyBudget r.1 r.2)) ∧
      LedgerCost B1 B2 greedyBudget :=
  ⟨G.budget, ⟨G.stage⟩, G.budget_cost hC⟩

/-- The `greedy` field, with `CertSize` supplied by the `cert` stage. -/
theorem greedy_of_components_cert (G : GreedyComponents B1 B2)
    {certBudget : Call → List Bool → ℕ}
    (cert : WordFunction (Call × List Bool) (fun r => prepWord B1 B2 r.1 r.2)
      (fun r => frame (certWord B1 B2 r.1 r.2)) (fun r => certBudget r.1 r.2))
    (hcost : LedgerCost B1 B2 certBudget) :
    ∃ greedyBudget : Call → List Bool → ℕ,
      Nonempty (WordFunction (Call × List Bool) (fun r => certWord B1 B2 r.1 r.2)
        (fun r => frame (greedyWord B1 B2 r.1 r.2)) (fun r => greedyBudget r.1 r.2)) ∧
      LedgerCost B1 B2 greedyBudget :=
  greedy_of_components G (certSize_of_cert cert hcost)

end NearQuarticWires.Greedy
