import Proof.Quartic.Program.Stages
import Proof.Quartic.Builder.Integer
import Proof.Quartic.Builder.Complete

/-!
# Step 3: the seed-fixing rounds

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, with the cost of `prop:time`
("Step 3 has `2S` child evaluations").

The `greedy` stage of the counter program (`Program.MachineComponents.greedy`) reads `certWord` and writes
`greedyWord`. This file reduces it to the control of the `S` rounds and the evaluation of one child.

* `greedyWord_eq_append`: the word after Step 3 is the word after Step 2 followed by `greedySuffix`, which is empty
  on a call that is not dispatched, and is the consistency bit followed by the chosen seed on a dispatched call.
* `greedySuffix_of_dispatch`: on a dispatched call every system on the seed path is consistent (`prop:sound`,
  step (1)), and the chosen seed is the seed of the integer greedy loop `Machine.chosenSeed S Ψ̃` on the integer
  objective `Ψ̃ = Builder.printedPotentialInt` (`Builder.chosenSeed_eq_machine`).
* A *child evaluation* (`ChildRequest`) is a dispatched call, its witness word and a seed prefix `π` of length at
  most `S`; its input word is `childInput` (the word after Step 2 followed by the framed prefix) and its value is
  `childObjective`, the integer `Ψ̃(π)`.
* `SeedLoop` is the control of the `S` rounds for an arbitrary integer objective `R` on child evaluations: from a
  word function computing `R`, it computes the word after Step 2 followed by `seedSuffix R`, i.e. the bit `1` and
  the seed of the greedy loop on `R`; each round makes two child evaluations and appends the bit of the child with
  the smaller value, ties going to `0`.
* `seedSuffix_childObjective`: for `R = childObjective` the suffix is exactly `greedySuffix`, so the `S` rounds on
  the child objective compute Step 3 (`Algorithm.CellCall.chosenSeed`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Greedy

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-! ## The word written by Step 3 -/

/-- The data appended by Step 3 (`sec:algorithm`, paper/paper.tex): on a dispatched call, the consistency bit of
the systems met on the seed path followed by the framed chosen seed; on every other call, nothing. -/
noncomputable def greedySuffix (B1 B2 : ℕ) (c : Call) (w : List Bool) : List Bool :=
  match dispatch B1 B2 c with
  | some p => bitWord (consistentBit (runCall c p w)) ++ frame (runCall c p w).chosenSeed
  | none => []

/-- The word after Step 3 is the word after Step 2 followed by `greedySuffix`. -/
theorem greedyWord_eq_append (c : Call) (w : List Bool) :
    greedyWord B1 B2 c w = certWord B1 B2 c w ++ greedySuffix B1 B2 c w := by
  unfold greedyWord certWord greedySuffix stageWord
  cases dispatch B1 B2 c with
  | some p => simp [List.append_assoc]
  | none => simp

theorem greedySuffix_of_not_dispatch {c : Call} (h : dispatch B1 B2 c = none) (w : List Bool) :
    greedySuffix B1 B2 c w = [] := by
  unfold greedySuffix
  rw [h]

/-! ## Dispatched calls -/

section Dispatched

variable {c : Call} {p : Selected c}

/-- A dispatched call has the shape read by the cell construction. -/
theorem shaped_of_dispatch (h : dispatch B1 B2 c = some p) : Builder.Shaped c :=
  Builder.Shaped.of_admitted (dispatch_admitted h).1

/-- The hypotheses of step (1) of `prop:sound` (paper/paper.tex) hold for the cell call of a
dispatched call and every witness word. -/
theorem reconstructionHypotheses_of_dispatch (h : dispatch B1 B2 c = some p) (w : List Bool) :
    (runCall c p w).ReconstructionHypotheses :=
  Builder.reconstructionHypotheses c (Cells.prepare_spec _ p.1 p.2) (shaped_of_dispatch h) w

/-- On a dispatched call, every system met on the seed path is consistent (paper/paper.tex: "by
`prop:sound` this never happens"). -/
theorem consistentBit_of_dispatch (h : dispatch B1 B2 c = some p) (w : List Bool) :
    consistentBit (runCall c p w) = true := by
  unfold consistentBit
  simp only [decide_eq_true_eq]
  exact Algorithm.CellCall.pathConsistent _ (reconstructionHypotheses_of_dispatch h w)

/-- On a dispatched call, the seed chosen in Step 3 is the seed of the integer greedy loop on the integer
objective `Ψ̃ = Builder.printedPotentialInt` (`sec:algorithm`, paper/paper.tex). -/
theorem chosenSeed_of_dispatch (h : dispatch B1 B2 c = some p) (w : List Bool) :
    (runCall c p w).chosenSeed =
      Machine.chosenSeed (runCall c p w).seedLength (Builder.printedPotentialInt (runCall c p w)) :=
  Builder.chosenSeed_eq_machine _ (reconstructionHypotheses_of_dispatch h w)

/-- The seed length `S = 2mℓ_f` of the cell call is the parameter `S` of `sec:params` (paper/paper.tex), the number of rounds of Step 3. -/
theorem seedLength_runCall (p : Selected c) (w : List Bool) : (runCall c p w).seedLength = p.1.S :=
  Cells.ParameterRules.seed_length (Cells.prepare_spec _ p.1 p.2)

/-- The data appended by Step 3 on a dispatched call: the bit `1` and the seed of the integer greedy loop. -/
theorem greedySuffix_of_dispatch (h : dispatch B1 B2 c = some p) (w : List Bool) :
    greedySuffix B1 B2 c w = bitWord true ++
      frame (Machine.chosenSeed (runCall c p w).seedLength (Builder.printedPotentialInt (runCall c p w))) := by
  unfold greedySuffix
  rw [h]
  dsimp only
  rw [consistentBit_of_dispatch h w, chosenSeed_of_dispatch h w]

end Dispatched

/-! ## The greedy loop reads the objective only at prefixes of length at most `S` -/

/-- The integer greedy loop of `S` rounds (`Machine.chosenSeed`) reads its objective only at prefixes of length at
most `S`: the children `π0`, `π1` of the prefixes `π` of length `i < S`. -/
theorem chosenSeed_congr (S : ℕ) (R R' : List Bool → ℤ) (hR : ∀ π : List Bool, π.length ≤ S → R π = R' π) :
    Machine.chosenSeed S R = Machine.chosenSeed S R' := by
  unfold Machine.chosenSeed NearCubicWires.WireExponent3_5.SeedFix.greedyLoop
  have key : ∀ i, i ≤ S → (NearCubicWires.WireExponent3_5.SeedFix.greedyStep R)^[i] [] =
      (NearCubicWires.WireExponent3_5.SeedFix.greedyStep R')^[i] [] ∧
      ((NearCubicWires.WireExponent3_5.SeedFix.greedyStep R)^[i] []).length = i := by
    intro i
    induction i with
    | zero => intro _; exact ⟨rfl, rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨heq, hlen⟩ := ih (by omega)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', heq]
      set q := (NearCubicWires.WireExponent3_5.SeedFix.greedyStep R')^[i] []
      have hq : q.length = i := heq ▸ hlen
      have ht : R (q ++ [true]) = R' (q ++ [true]) := hR _ (by simp [hq]; omega)
      have hf : R (q ++ [false]) = R' (q ++ [false]) := hR _ (by simp [hq]; omega)
      refine ⟨?_, ?_⟩
      · unfold NearCubicWires.WireExponent3_5.SeedFix.greedyStep
        rw [ht, hf]
      · unfold NearCubicWires.WireExponent3_5.SeedFix.greedyStep
        simp [hq]
  exact (key S le_rfl).1

/-! ## Child evaluations -/

/-- **A child evaluation of Step 3** (`sec:algorithm`, paper/paper.tex): a dispatched call, its witness word, and a
seed prefix `π` of length at most `S` whose objective `Ψ̃(π)` is to be computed. -/
structure ChildRequest (B1 B2 : ℕ) where
  /-- The call. -/
  call : Call
  /-- The witness word. -/
  witness : List Bool
  /-- The parameters selected for the call. -/
  selected : Selected call
  /-- The call is dispatched to Steps 1–5. -/
  dispatched : dispatch B1 B2 call = some selected
  /-- The seed prefix `π`. -/
  seedPrefix : List Bool
  /-- `|π| ≤ S`. -/
  prefix_le : seedPrefix.length ≤ (runCall call selected witness).seedLength

/-- The cell call of `sec:algorithm` on which the child is evaluated. -/
noncomputable def ChildRequest.cellCall (q : ChildRequest B1 B2) : Algorithm.CellCall :=
  runCall q.call q.selected q.witness

/-- The input word of a child evaluation: the word after Step 2 (`certWord`), followed by the framed prefix `π`. -/
noncomputable def childInput (q : ChildRequest B1 B2) : List Bool :=
  certWord B1 B2 q.call q.witness ++ frame q.seedPrefix

/-- **The child objective** (`sec:algorithm`, paper/paper.tex): the integer `Ψ̃(π)` of the prefix,
`Σ_{z ∈ Z_c} Σ_σ κ_σ Σ_δ v_{z,σ,δ}` (`Builder.printedPotentialInt`). -/
noncomputable def childObjective (q : ChildRequest B1 B2) : ℤ :=
  Builder.printedPotentialInt q.cellCall q.seedPrefix

/-! ## The rounds for an arbitrary objective -/

/-- The number `S` of rounds of Step 3 on a call: the parameter `S` of `sec:params` on a dispatched call, and `0`
on every other call. -/
noncomputable def seedRounds (B1 B2 : ℕ) (c : Call) : ℕ :=
  match dispatch B1 B2 c with
  | some p => p.1.S
  | none => 0

theorem seedRounds_of_dispatch {c : Call} {p : Selected c} (h : dispatch B1 B2 c = some p) (w : List Bool) :
    seedRounds B1 B2 c = (runCall c p w).seedLength := by
  unfold seedRounds
  rw [h, seedLength_runCall]

/-- An integer objective `R` on the child evaluations of a dispatched call, as a function of the prefix: `R` at
prefixes of length at most `S`, and `0` beyond (the greedy loop never reads these). -/
noncomputable def prefixObjective (R : ChildRequest B1 B2 → ℤ) (c : Call) (w : List Bool) (p : Selected c)
    (h : dispatch B1 B2 c = some p) (π : List Bool) : ℤ := by
  classical
  exact if hπ : π.length ≤ (runCall c p w).seedLength then R ⟨c, w, p, h, π, hπ⟩ else 0

/-- The data appended by the `S` rounds on the objective `R`: on a dispatched call, the bit `1` followed by the
framed seed of the greedy loop on `R`; on every other call, nothing. -/
noncomputable def seedSuffix (B1 B2 : ℕ) (R : ChildRequest B1 B2 → ℤ) (c : Call) (w : List Bool) : List Bool :=
  match hd : dispatch B1 B2 c with
  | some p => bitWord true ++ frame (Machine.chosenSeed (runCall c p w).seedLength (prefixObjective R c w p hd))
  | none => []

theorem seedSuffix_of_dispatch (R : ChildRequest B1 B2 → ℤ) {c : Call} {p : Selected c}
    (h : dispatch B1 B2 c = some p) (w : List Bool) :
    seedSuffix B1 B2 R c w =
      bitWord true ++ frame (Machine.chosenSeed (runCall c p w).seedLength (prefixObjective R c w p h)) := by
  unfold seedSuffix
  split
  · rename_i p' hd
    have e : p' = p := Option.some.inj (hd.symm.trans h)
    subst e
    rfl
  · rename_i hd
    rw [h] at hd
    exact absurd hd (by simp)

theorem seedSuffix_of_not_dispatch (R : ChildRequest B1 B2 → ℤ) {c : Call} (h : dispatch B1 B2 c = none)
    (w : List Bool) : seedSuffix B1 B2 R c w = [] := by
  unfold seedSuffix
  split
  · rename_i p' hd
    rw [h] at hd
    exact absurd hd (by simp)
  · rfl

/-- **The `S` rounds on the child objective are Step 3** (`sec:algorithm`, paper/paper.tex): with
`R = childObjective`, the data appended by the rounds is exactly `greedySuffix`, the consistency bit and the seed
`Algorithm.CellCall.chosenSeed` chosen by the algorithm. -/
theorem seedSuffix_childObjective (c : Call) (w : List Bool) :
    seedSuffix B1 B2 childObjective c w = greedySuffix B1 B2 c w := by
  cases hd : dispatch B1 B2 c with
  | none => rw [seedSuffix_of_not_dispatch _ hd, greedySuffix_of_not_dispatch hd]
  | some p =>
    rw [seedSuffix_of_dispatch _ hd, greedySuffix_of_dispatch hd]
    congr 2
    apply chosenSeed_congr
    intro π hπ
    unfold prefixObjective
    rw [dif_pos hπ]
    rfl

/-- **The word after Step 3** is the word after Step 2 followed by the data of the `S` rounds on the child
objective. -/
theorem greedyWord_eq_seedSuffix (c : Call) (w : List Bool) :
    greedyWord B1 B2 c w = certWord B1 B2 c w ++ seedSuffix B1 B2 childObjective c w := by
  rw [greedyWord_eq_append, seedSuffix_childObjective]

/-! ## The control of the rounds -/

/-- **The control of the `S` rounds of Step 3** (paper/paper.tex, with `prop:time`), for an arbitrary integer objective `R` on the child evaluations.

Given a word function `child` that maps `childInput q` (the word after Step 2 followed by the framed prefix `π`) to
`intWord (R q)` within `childBudget q ≤ childBound c w` steps, `program` maps the word after Step 2 to the framed
word after Step 2 followed by `seedSuffix R`: on a call whose word carries the tag `0` it copies the word; on a
dispatched call it reads `S` from the parameters, starts from the empty prefix and, in each of the `S` rounds,
evaluates the two children `π0`, `π1`, compares the two integers and appends the bit of the smaller one (on ties
`0`), and finally appends the bit `1` and the framed seed. Each round costs two child evaluations, the copies of
the word after Step 2 into the two child inputs, and the comparison, so the cost is
`K (S + 1) (childBound + |certWord| + S + 1)`. -/
structure SeedLoop (B1 B2 : ℕ) where
  /-- The constant of the cost. -/
  K : ℕ
  /-- The program of the rounds, for every objective and every word function computing it. -/
  program : ∀ (R : ChildRequest B1 B2 → ℤ) (childBudget : ChildRequest B1 B2 → ℕ)
      (childBound : Call → List Bool → ℕ),
    WordFunction (ChildRequest B1 B2) childInput (fun q => NearCubicGates.Close.Interfaces.intWord (R q))
      childBudget →
    (∀ q : ChildRequest B1 B2, childBudget q ≤ childBound q.call q.witness) →
    WordFunction (Call × List Bool) (fun r => certWord B1 B2 r.1 r.2)
      (fun r => frame (certWord B1 B2 r.1 r.2 ++ seedSuffix B1 B2 R r.1 r.2))
      (fun r => K * (seedRounds B1 B2 r.1 + 1) *
        (childBound r.1 r.2 + (certWord B1 B2 r.1 r.2).length + seedRounds B1 B2 r.1 + 1))

end NearQuarticWires.Greedy
