import Proof.Quartic.Greedy.Stage
import Proof.Quartic.Machine.GammaInterface
import Proof.Gates.Interfaces.CounterFormats

/-!
# Step 3: one child evaluation

Paper: Step 3 of `sec:algorithm`, paper/paper.tex; `cor:conditional`;
`lem:residue`; `prop:time`.

One child evaluation computes, for a prefix `π`, the integer
`Ψ̃(π) = Σ_{z ∈ Z_c} Σ_σ κ_σ Σ_δ v_{z,σ,δ}` (`childObjective`). The paper computes it by three subroutines:

1. **Coefficients** (`cor:conditional`): the integer weights `2^S c_π(w)` of the closed walks `w`
   (`Algorithm.CellCall.walkWeight`); one weight is the target `Machine.gammaTarget` of a `Machine.GammaRequest`
   (`gammaTarget_gammaRequest`).
2. **Printing and recovery** (`lem:print`(a), `lem:residue`): for every `σ` with `κ_σ ≠ 0`, every `p ∈ 𝒫` and
   every residue vector, the table over all columns of the recovered counts `𝒩(z)`, the centred residues modulo
   `p^e` of the printed integers `Π(z)` (`printTable`). Only `Π(z)` modulo `p^e` enters Step 3, so the table is
   printed modulo `p^e`: every entry has at most `e lg p` bits.
3. **Solving** (Step 3): the exact system on the box `Bx(δ)` whose right sides are the recovered
   counts; `v_{z,σ,δ} = H̃(0)`.

The exact systems of the base library (`Interfaces.Formats.SysReq`) have natural right sides, while the counts of
the signed weights `2^S c_π(w)` are signed. The weights are therefore split into their positive and negative parts
(`splitWeight`): each part is a nonnegative weight whose recovered counts and class functions are nonnegative, and
`v_{z,σ,δ}` is the difference of the two values (`classValueInt_split`, `childObjective_split`).

The child evaluation is the composition of two stages (`ChildComponents`): the coefficient table (`gammaWord`) and
the reconstruction (printing, solving and the `κ`-weighted sum), composed by `Program.WordFunction.pipe`
(`ChildComponents.child`). The subroutines that the two stages call are typed by `GammaTableControl` and
`ReconstructControl`: one coefficient (`Machine.GammaProgramObligation`), one table of recovered counts
(`PrintRequest`) and one exact system (`Interfaces.Formats.SolveMachine`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Greedy

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-! ## The closed walks -/

/-- The closed walks `w = (u_1, v_1, …, u_m, v_m)` of `sec:cycle` (paper/paper.tex) with `m = 4`, in
the order of their base-`N` index. -/
def walkList (N : ℕ) : List (Cycle.Walk N Algorithm.traceOrder) :=
  List.ofFn (finFunctionFinEquiv (m := N) (n := 2 * Algorithm.traceOrder)).symm

theorem walkList_length (N : ℕ) : (walkList N).length = N ^ (2 * Algorithm.traceOrder) := by
  simp [walkList]

theorem mem_walkList (N : ℕ) (w : Cycle.Walk N Algorithm.traceOrder) : w ∈ walkList N := by
  apply List.mem_ofFn.mpr
  exact ⟨finFunctionFinEquiv w, Equiv.symm_apply_apply _ w⟩

theorem walkList_nodup (N : ℕ) : (walkList N).Nodup :=
  List.nodup_ofFn.mpr (Equiv.injective _)

/-! ## Coefficients (`cor:conditional`) -/

/-- The prefix number of `π` (its bits, lowest first) is below `2^{|π|}`. -/
theorem prefixValue_lt (π : List Bool) : Algorithm.CellCall.prefixValue π < 2 ^ π.length := by
  induction π with
  | nil => simp [Algorithm.CellCall.prefixValue]
  | cons b bs ih =>
    simp only [Algorithm.CellCall.prefixValue, List.length_cons, pow_succ]
    split <;> omega

/-- The coefficient request of `cor:conditional` (paper/paper.tex) for the walk `w` at the prefix of
a child evaluation: the seed parameters of the cell call, the prefix and the walk. -/
noncomputable def gammaRequest (q : ChildRequest B1 B2) (w : Cycle.Walk q.cellCall.seed.N Algorithm.traceOrder) :
    Machine.GammaRequest where
  parameters := q.cellCall.seed
  prefixLength := q.seedPrefix.length
  prefixCode := Algorithm.CellCall.prefixValue q.seedPrefix
  walk := w
  prefixFits := q.prefix_le
  prefixCodeFits := prefixValue_lt _

/-- The target of the coefficient request is the walk weight `2^S c_π(w)` of the cell call. -/
theorem gammaTarget_gammaRequest (q : ChildRequest B1 B2) (w : Cycle.Walk q.cellCall.seed.N Algorithm.traceOrder) :
    Machine.gammaTarget (gammaRequest q w) = q.cellCall.walkWeight q.seedPrefix w := rfl

/-- The coefficient table of a child evaluation: `2^S c_π(w)` for every closed walk, in the order of `walkList`. -/
noncomputable def gammaTable (q : ChildRequest B1 B2) : List ℤ :=
  (walkList q.cellCall.seed.N).map (q.cellCall.walkWeight q.seedPrefix)

/-- The framed coefficient table. -/
noncomputable def gammaTableWord (q : ChildRequest B1 B2) : List Bool :=
  frame (listWord NearCubicGates.Close.Interfaces.intWord (gammaTable q))

/-- The word after the coefficient stage: the child input followed by the framed coefficient table. -/
noncomputable def gammaWord (q : ChildRequest B1 B2) : List Bool :=
  childInput q ++ gammaTableWord q

/-! ## The signed split -/

section Split

variable (C : Algorithm.CellCall)

/-- The positive (`s = true`) and negative (`s = false`) parts of the walk weights `2^S c_π(w)`. -/
noncomputable def splitWeight (π : List Bool) (s : Bool) (w : Cycle.Walk C.seed.N Algorithm.traceOrder) : ℤ :=
  if s then max (C.walkWeight π w) 0 else max (-C.walkWeight π w) 0

theorem walkWeight_split (π : List Bool) (w : Cycle.Walk C.seed.N Algorithm.traceOrder) :
    C.walkWeight π w = splitWeight C π true w - splitWeight C π false w := by
  simp only [splitWeight, if_true, Bool.false_eq_true, if_false]
  exact (max_zero_sub_max_neg_zero_eq_self _).symm

theorem splitWeight_nonneg (π : List Bool) (s : Bool) (w : Cycle.Walk C.seed.N Algorithm.traceOrder) :
    0 ≤ splitWeight C π s w := by
  unfold splitWeight
  split <;> exact le_max_right _ _

theorem splitWeight_le_abs (π : List Bool) (s : Bool) (w : Cycle.Walk C.seed.N Algorithm.traceOrder) :
    splitWeight C π s w ≤ |C.walkWeight π w| := by
  unfold splitWeight
  split
  · exact max_le (le_abs_self _) (abs_nonneg _)
  · exact max_le (neg_le_abs _) (abs_nonneg _)

/-- The class function of Step 3 for an arbitrary integer weight `g` on the walks (`prop:sound`, paper/paper.tex): `y ↦ Σ_{w : mask_w(z) = 1, E(w) = δ, Y(w) = y} g(w)`. -/
noncomputable def classValueOf (g : Cycle.Walk C.seed.N Algorithm.traceOrder → ℤ) (z : Fin C.ncol)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (y : Fin 2 → ℤ) : ℤ := by
  classical
  exact ∑ w, if C.walkMask z w = 1 ∧ C.HasDigits z σ w δ ∧ C.walkSums z σ w = y then g w else 0

/-- The value `v^±_{z,σ,δ} = H̃^±(0)` of the part `s` of the weights (Step 3 of `sec:algorithm`). -/
noncomputable def splitValue (π : List Bool) (s : Bool) (z : Fin C.ncol) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) : ℤ :=
  classValueOf C (splitWeight C π s) z σ δ 0

/-- The integer `H_{z,σ,δ}(0)` is the difference of the values of the two parts of the weights. -/
theorem classValueInt_split (π : List Bool) (z : Fin C.ncol) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) :
    Builder.classValueInt C π z σ δ = splitValue C π true z σ δ - splitValue C π false z σ δ := by
  classical
  unfold Builder.classValueInt splitValue classValueOf
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs
  · exact walkWeight_split C π w
  · simp

/-- `lem:residue` (paper/paper.tex) for an arbitrary integer weight `g`: the printed integer `Π(z)`
for the pattern `σ`, the prime `p` and the residue vector `(δ mod p, ρ_Y)`. -/
noncomputable def printedCountOf (g : Cycle.Walk C.seed.N Algorithm.traceOrder → ℤ) (z : Fin C.ncol)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (p : ℕ) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (ρY : Fin 2 → ℤ) : ℤ :=
  Walks.residuePolynomial g
    (Walks.walkMaskPoly Algorithm.traceOrder_pos (C.column z).structural (C.column z).tau (C.column z).Xmax
      (C.column z).X)
    p C.e (C.residueForms z σ) (C.residueTarget z p δ ρY)

theorem printedCount_eq_of (π : List Bool) (z : Fin C.ncol) (σ : Cycle.SignPattern Algorithm.traceOrder) (p : ℕ)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) (ρY : Fin 2 → ℤ) :
    C.printedCount π z σ p δ ρY = printedCountOf C (C.walkWeight π) z σ p δ ρY := rfl

/-- `lem:residue` (paper/paper.tex) for an arbitrary integer weight: the recovered count `𝒩(z)`,
the centred residue of `Π(z)` modulo `p^e`. -/
noncomputable def recoveredCountOf (g : Cycle.Walk C.seed.N Algorithm.traceOrder → ℤ) (z : Fin C.ncol)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (p : ℕ) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (ρY : Fin 2 → ℤ) : ℤ :=
  Walks.centeredResidue ((p : ℤ) ^ C.e) (printedCountOf C g z σ p δ ρY)

end Split

/-- **The child objective with the signed split** (`sec:algorithm`, paper/paper.tex):
`Ψ̃(π) = Σ_{z ∈ Z_c} Σ_σ κ_σ Σ_δ (v⁺_{z,σ,δ} - v⁻_{z,σ,δ})`. -/
theorem childObjective_split (q : ChildRequest B1 B2) :
    childObjective q = ∑ z ∈ q.cellCall.certifiedColumns, ∑ σ : Cycle.SignPattern Algorithm.traceOrder,
      Cycle.kappa Algorithm.traceOrder σ * ∑ δ ∈ q.cellCall.digitVectors z,
        (splitValue q.cellCall q.seedPrefix true z σ δ - splitValue q.cellCall q.seedPrefix false z σ δ) := by
  unfold childObjective Builder.printedPotentialInt
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun δ _ => classValueInt_split _ _ _ _ _

/-! ## The subroutines -/

/-- **One table of recovered counts** (`lem:print`(a), paper/paper.tex, and `lem:residue`): for a
child evaluation, a part `s` of the weights, a pattern `σ`, a prime `p` and a residue vector `(δ mod p, ρ_Y)`. -/
structure PrintRequest (B1 B2 : ℕ) where
  /-- The child evaluation. -/
  child : ChildRequest B1 B2
  /-- The part of the weights: positive (`true`) or negative (`false`). -/
  sign : Bool
  /-- The pattern `σ`. -/
  pattern : Cycle.SignPattern Algorithm.traceOrder
  /-- The prime `p ∈ 𝒫`. -/
  prime : ℕ
  /-- The prime belongs to the set `𝒫` of the cell call (`sec:params`, paper/paper.tex). This field
  is a proof: it carries no data and is not part of the index word `printIndexWord`. -/
  prime_mem : prime ∈ child.cellCall.primes
  /-- The digit vector `δ`, whose residue `ρ_E = δ mod p` is printed. -/
  digits : Fin 2 → Fin (child.cellCall.J + 1) → ℤ
  /-- The residue vector `ρ_Y`. -/
  residues : Fin 2 → ℤ

/-- The indices of a printed table: the part, the pattern, the prime, the digit vector and the residue vector. -/
noncomputable def printIndexWord (r : PrintRequest B1 B2) : List Bool :=
  bitWord r.sign ++ listWord bitWord (List.ofFn r.pattern) ++ natWord r.prime ++
    listWord NearCubicGates.Close.Interfaces.intWord
      (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin (r.child.cellCall.J + 1) => r.digits i j).flatten ++
    listWord NearCubicGates.Close.Interfaces.intWord (List.ofFn r.residues)

/-- The input word of a printed table: the word after parameter preparation (the call, the parameters and the
witness prefix, from which the column data are computed), the framed coefficient table, and the indices. It does not
contain the `2^{n-k}` certified-column bits. -/
noncomputable def printInput (r : PrintRequest B1 B2) : List Bool :=
  prepWord B1 B2 r.child.call r.child.witness ++ gammaTableWord r.child ++ printIndexWord r

/-- The table of recovered counts `z ↦ 𝒩(z)` over all `2^{n-k}` columns, for the part `s` of the weights: the
centred residues modulo `p^e` of the printed integers `Π(z)` (`lem:print`(a): one table in time `2^{n-k} poly(n)`;
`lem:residue`). -/
noncomputable def printTable (r : PrintRequest B1 B2) : List ℤ :=
  List.ofFn fun z : Fin r.child.cellCall.ncol =>
    recoveredCountOf r.child.cellCall (splitWeight r.child.cellCall r.child.seedPrefix r.sign) z r.pattern r.prime
      r.digits r.residues

/-! ## The two stages of a child evaluation -/

/-- `prop:time`: a child prints at most `2 · 4^m · |𝒫| · P^{2(J+1)} · P^2 ≤ 2 · 4^m · P^{2(J+1)+3}`
tables (both parts of the weights; `4^m` patterns `σ`, the primes `p ≤ P`, the digit vectors with entries in
`(-h_E, h_E)`, `2h_E - 1 < p ≤ P`, and the residue vectors `ρ_Y`). -/
noncomputable def tableCount (q : ChildRequest B1 B2) : ℕ :=
  2 * 4 ^ Algorithm.traceOrder * q.selected.1.P ^ (2 * (q.cellCall.J + 1) + 3)

/-- `prop:time`: a child solves at most `2 · 2^{n-k} · 4^m · P^{2(J+1)}` exact systems. -/
noncomputable def systemCount (q : ChildRequest B1 B2) : ℕ :=
  2 * q.cellCall.ncol * 4 ^ Algorithm.traceOrder * q.selected.1.P ^ (2 * (q.cellCall.J + 1))

/-- `prop:time`: each system has at most `|𝒫| · P^2 ≤ P^3` equations, i.e. recovered counts. -/
noncomputable def rowCount (q : ChildRequest B1 B2) : ℕ := q.selected.1.P ^ 3

/-- **The coefficient stage** (Step 3; `prop:time`): for each of the `N^{2m} = 2^{mk}`
closed walks, one coefficient `2^S c_π(w)` (a `Machine.GammaRequest`, computed in `(Q+1)^{2m} poly(n)` time). From a
word function computing one coefficient, `program` writes the framed coefficient table `gammaWord`; each walk costs
one coefficient evaluation and a polynomial overhead for its request and its entry of the table, and the child input
is read once. -/
structure GammaTableControl (B1 B2 : ℕ) where
  /-- The constant of the cost. -/
  K : ℕ
  /-- The exponent of the polynomial overhead per walk. -/
  e : ℕ
  /-- The table program, for every word function computing one coefficient. -/
  program : ∀ (gammaBudget : Machine.GammaRequest → ℕ) (gammaBound : Call → List Bool → ℕ),
    WordFunction Machine.GammaRequest Machine.gammaRequestWord
      (fun r => NearCubicGates.Close.Interfaces.intWord (Machine.gammaTarget r)) gammaBudget →
    (∀ (q : ChildRequest B1 B2) (w : Cycle.Walk q.cellCall.seed.N Algorithm.traceOrder),
      gammaBudget (gammaRequest q w) ≤ gammaBound q.call q.witness) →
    WordFunction (ChildRequest B1 B2) childInput (fun q => frame (gammaWord q))
      (fun q => K * ((q.cellCall.seed.N ^ (2 * Algorithm.traceOrder) + 1) *
        (gammaBound q.call q.witness + (q.call.n + 1) ^ e + q.seedPrefix.length) + (childInput q).length + 1))

/-- **The reconstruction stage** (Step 3; `prop:time`): from the coefficient table,
print the tables of recovered counts `𝒩` for both parts of the weights, every `σ` with `κ_σ ≠ 0`, every `p ∈ 𝒫` and
every residue vector (at most `tableCount` tables); solve the exact systems on the boxes `Bx(δ)` at the certified
columns (at most `systemCount` systems of at most `rowCount` equations; the indices of each table and each system
have polynomial size `(n+1)^{e₀}`), with the values of the solver (`childObjective_solved`); and return
`Ψ̃(π) = Σ_{z ∈ Z_c} Σ_σ κ_σ Σ_δ (v⁺ - v⁻)`. From a word function for one table and an exact solver (the base
`Interfaces.Formats.SolveMachine`), `program` maps `gammaWord` to `intWord Ψ̃(π)`. Each table costs one printing,
the copy of its input (`prepWord`, the coefficient table and its indices) and its `2^{n-k}` records; each system
costs its rows and one solve; the cost carries a polynomial factor for the sorting and gathering of the records. -/
structure ReconstructControl (B1 B2 : ℕ) where
  /-- The constant of the cost. -/
  K : ℕ
  /-- The exponent of the polynomial factor. -/
  e : ℕ
  /-- The exponent of the size of the table indices and of the systems. -/
  e₀ : ℕ
  /-- The reconstruction program, for every word function computing one table and every exact solver. -/
  program : ∀ (printBudget : PrintRequest B1 B2 → ℕ) (solver : Formats.SolveMachine)
      (printBound solveBound : Call → List Bool → ℕ),
    WordFunction (PrintRequest B1 B2) printInput
      (fun r => listWord NearCubicGates.Close.Interfaces.intWord (printTable r)) printBudget →
    (∀ r : PrintRequest B1 B2, (printIndexWord r).length ≤ (r.child.call.n + 1) ^ e₀ →
      printBudget r ≤ printBound r.child.call r.child.witness) →
    (∀ (q : ChildRequest B1 B2) (s : Formats.SysReq), (Formats.sysWord s).length ≤ (q.call.n + 1) ^ e₀ →
      solver.budget s ≤ solveBound q.call q.witness) →
    WordFunction (ChildRequest B1 B2) gammaWord (fun q => NearCubicGates.Close.Interfaces.intWord (childObjective q))
      (fun q => K * (q.call.n + 1) ^ e *
        (tableCount q * (printBound q.call q.witness + (prepWord B1 B2 q.call q.witness).length +
            (gammaTableWord q).length + q.cellCall.ncol + (q.call.n + 1) ^ e₀) +
          systemCount q * (rowCount q + solveBound q.call q.witness + 1) +
          (gammaWord q).length + 1))

/-- **The components of one child evaluation**: the coefficient stage and the reconstruction stage, with a common
bound on their costs that is a ledger cost. -/
structure ChildComponents (B1 B2 : ℕ) where
  /-- The cost of the coefficient stage. -/
  gammaBudget : ChildRequest B1 B2 → ℕ
  /-- The coefficient stage. -/
  gammaStage : WordFunction (ChildRequest B1 B2) childInput (fun q => frame (gammaWord q)) gammaBudget
  /-- The cost of the reconstruction stage. -/
  reconstructBudget : ChildRequest B1 B2 → ℕ
  /-- The reconstruction stage. -/
  reconstructStage : WordFunction (ChildRequest B1 B2) gammaWord
    (fun q => NearCubicGates.Close.Interfaces.intWord (childObjective q)) reconstructBudget
  /-- A bound on the cost of both stages on the child evaluations of a call. -/
  childBound : Call → List Bool → ℕ
  bound_spec : ∀ q : ChildRequest B1 B2, gammaBudget q + reconstructBudget q ≤ childBound q.call q.witness
  /-- The bound is a ledger cost. -/
  childCost : LedgerCost B1 B2 childBound

namespace ChildComponents

variable (K : ChildComponents B1 B2)

/-- **One child evaluation**: the coefficient stage followed by the reconstruction stage
(`Program.WordFunction.pipe`). -/
noncomputable def child : WordFunction (ChildRequest B1 B2) childInput
    (fun q => NearCubicGates.Close.Interfaces.intWord (childObjective q))
    (fun q => 4 * K.gammaBudget q + 4 * K.reconstructBudget q + 12) :=
  WordFunction.pipe K.gammaStage K.reconstructStage

/-- **The components of the `greedy` stage** from the control of the `S` rounds and the two stages of a child. -/
noncomputable def toGreedy (loop : SeedLoop B1 B2) : GreedyComponents B1 B2 where
  loop := loop
  childBudget := fun q => 4 * K.gammaBudget q + 4 * K.reconstructBudget q + 12
  child := K.child
  childBound := fun c w => 4 * K.childBound c w + 12
  childBound_spec := fun q => by
    have := K.bound_spec q
    omega
  childCost := by
    obtain ⟨Kc, e, h⟩ := K.childCost
    refine ⟨4 * Kc + 12, e, fun c w => ?_⟩
    have h1 := h c w
    have h3 : 1 ≤ ((callWord c).length + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    nlinarith

end ChildComponents

/-- **The `greedy` field from the control of the rounds and the two stages of a child** (Step 3, paper/paper.tex, with `prop:time`): with the `cert` stage, a word function from `certWord` to
`frame greedyWord` with a ledger cost. -/
theorem greedy_of_child (loop : SeedLoop B1 B2) (K : ChildComponents B1 B2)
    {certBudget : Call → List Bool → ℕ}
    (cert : WordFunction (Call × List Bool) (fun r => prepWord B1 B2 r.1 r.2)
      (fun r => frame (certWord B1 B2 r.1 r.2)) (fun r => certBudget r.1 r.2))
    (hcost : LedgerCost B1 B2 certBudget) :
    ∃ greedyBudget : Call → List Bool → ℕ,
      Nonempty (WordFunction (Call × List Bool) (fun r => certWord B1 B2 r.1 r.2)
        (fun r => frame (greedyWord B1 B2 r.1 r.2)) (fun r => greedyBudget r.1 r.2)) ∧
      LedgerCost B1 B2 greedyBudget :=
  greedy_of_components_cert (K.toGreedy loop) cert hcost

end NearQuarticWires.Greedy
