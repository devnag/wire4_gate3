import Proof.Quartic.Builder.CounterMath
import Proof.Quartic.Cells.AsymptoticsRuntime
import Proof.Quartic.Program.Pipe

/-!
# The stages of the counter program and their exact specifications

Paper: `sec:algorithm`, paper/paper.tex (parameters, witness, Steps 1–5) and `prop:time` (the cost of each step).

The counter program of `thm:counter` is the composition of five stages, each one word function on
(call, witness word):

| stage | paper | computes | cost (`prop:time`) |
|---|---|---|---|
| `prep` | `sec:params`, witness | the §9 parameters `Cells.prepare` and the witness prefix | polynomial |
| `cert` | Steps 1–2 | the certified columns `Z_c` | three-term envelope |
| `greedy` | Step 3 | the chosen seed and path consistency | three-term envelope |
| `main` | Step 4 | the sampled totals over `Z_c` | three-term envelope |
| `output` | Step 5 | the interval `(p̂, κ̂)` | polynomial |

Each stage reads the word written by the previous one and writes the next word framed (`frame`), so that the
stages compose by `WordFunction.pipe`. A call is *dispatched* when it is normalized (`Transfer.Admitted4`), has
`W ≠ 0`, and the exact rules select parameters; a dispatched call carries the tag `true` and the data of the
algorithm, every other call carries the tag `false` and its final interval, which every later stage passes on.

The stage words name the paper's quantities: `parametersWord` (the record `Cells.Parameters`), `witnessPrefix`
(the bits (W1)–(W3) of the witness), `certifiedBits` (`Z_c`), `consistentBit` and
`Algorithm.CellCall.chosenSeed` (Step 3), `acceptTotal` and `maskTotal` (Step 4). The word after `main` carries
exactly the inputs of Step 5.
-/

set_option autoImplicit false

namespace NearQuarticWires.Program

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-! ## The value returned on every call -/

/-- The interval returned by the counter: the value `v` on normalized calls (`Transfer.Admitted4`, the calls of
`thm:counter`), and the sound default `(1/2, 1/2)` of `sec:params` on every other call. -/
noncomputable def admittedValue (B1 B2 : ℕ) (v : Call → List Bool → ℚ × ℚ) (c : Call) (w : List Bool) : ℚ × ℚ := by
  classical
  exact if Transfer.Admitted4 B1 B2 c then v c w else Algorithm.soundDefault

theorem admittedValue_of_admitted {B1 B2 : ℕ} (v : Call → List Bool → ℚ × ℚ) {c : Call}
    (h : Transfer.Admitted4 B1 B2 c) (w : List Bool) : admittedValue B1 B2 v c w = v c w := by
  unfold admittedValue
  rw [if_pos h]

theorem admittedValue_of_not_admitted {B1 B2 : ℕ} (v : Call → List Bool → ℚ × ℚ) {c : Call}
    (h : ¬ Transfer.Admitted4 B1 B2 c) (w : List Bool) : admittedValue B1 B2 v c w = Algorithm.soundDefault := by
  unfold admittedValue
  rw [if_neg h]

/-! ## Dispatch -/

/-- The parameters selected for a call by the exact rules of `sec:params`, together with the selection. -/
abbrev Selected (c : Call) : Type := {p : Cells.Parameters // Cells.prepare (Builder.callInput c) = some p}

/-- **Dispatch** (`sec:params`): a normalized call with `W ≠ 0` whose parameters are selected by
`Cells.prepare` proceeds to Steps 1–5; every other call is answered directly. -/
noncomputable def dispatch (B1 B2 : ℕ) (c : Call) : Option (Selected c) := by
  classical
  exact if Transfer.Admitted4 B1 B2 c ∧ Transfer.callWires c ≠ 0 then
      match h : Cells.prepare (Builder.callInput c) with
      | some p => some ⟨p, h⟩
      | none => none
    else none

theorem dispatch_admitted {B1 B2 : ℕ} {c : Call} {p : Selected c} (h : dispatch B1 B2 c = some p) :
    Transfer.Admitted4 B1 B2 c ∧ Transfer.callWires c ≠ 0 := by
  classical
  unfold dispatch at h
  by_cases hc : Transfer.Admitted4 B1 B2 c ∧ Transfer.callWires c ≠ 0
  · exact hc
  · rw [if_neg hc] at h
    exact absurd h (by simp)

theorem dispatch_of_not_admitted {B1 B2 : ℕ} {c : Call} (h : ¬ Transfer.Admitted4 B1 B2 c) :
    dispatch B1 B2 c = none := by
  classical
  unfold dispatch
  rw [if_neg (fun hc => h hc.1)]

/-- The cell call of `sec:algorithm` of a dispatched call and a witness word: the call on the
cells of the partition named by the witness, with the parameters `p` (`Builder.cellCall`). -/
noncomputable def runCall (c : Call) (p : Selected c) (w : List Bool) : Algorithm.CellCall :=
  Builder.cellCall c (Cells.prepare_spec _ p.1 p.2) w

/-! ## The words of the stages -/

/-- The record `Cells.Parameters` of `sec:params` as a word: every natural field by `natWord`,
every rational field by `ratWord`, the prime set `𝒫` in increasing order and the factor list by `listWord`. -/
def parametersWord (p : Cells.Parameters) : List Bool :=
  natWord p.lambda ++ natWord p.mu ++ natWord p.m ++ natWord p.r ++ natWord p.s ++ natWord p.b ++
    natWord p.k ++ natWord p.N ++ natWord p.Jmax ++ natWord p.T ++ natWord p.tau ++ natWord p.U ++
    natWord p.Xmax ++ natWord p.dstar ++ natWord p.omega1 ++ natWord p.omega2 ++ natWord p.MF ++
    natWord p.Q ++ natWord p.ellf ++ natWord p.S ++ natWord p.NatAtoms ++ natWord p.childCap ++
    natWord p.Uocc ++ natWord p.Dmax ++ natWord p.BN ++ natWord p.P ++ natWord p.e ++ natWord p.hE ++
    natWord p.h ++ natWord p.Lw ++ ratWord p.pi0 ++ ratWord p.eta ++ natWord p.Qexp ++
    listWord natWord (p.primes.sort (· ≤ ·)) ++ natWord p.Dprime ++ natWord p.L2 ++ natWord p.M1 ++
    natWord p.J ++ natWord p.A ++ natWord p.Lambda ++ ratWord p.ell0 ++ listWord natWord p.factors

/-- The number of witness bits read by the algorithm (`sec:algorithm`, paper/paper.tex): `k + (J + 1)(G_1 + G_2)`. -/
def witnessReadLength (c : Call) (p : Cells.Parameters) : ℕ :=
  p.k + (p.J + 1) * (Builder.occurrences c 0 + Builder.occurrences c 1)

/-- The witness prefix (W1)–(W3) (`sec:algorithm`): the first `k + (J + 1)(G_1 + G_2)` bits of the witness word,
missing bits read as zeros (`Algorithm.witnessBit`). -/
def witnessPrefix (c : Call) (p : Cells.Parameters) (w : List Bool) : List Bool :=
  List.ofFn fun i : Fin (witnessReadLength c p) => Algorithm.witnessBit w i

/-- Step 2 of `sec:algorithm`: the set `Z_c` of certified columns, one bit per column. -/
noncomputable def certifiedBits (C : Algorithm.CellCall) : List Bool := by
  classical
  exact List.ofFn fun z : Fin C.ncol => decide (z ∈ C.certifiedColumns)

/-- Step 3 of `sec:algorithm`: whether every system met on the seed path is consistent. -/
noncomputable def consistentBit (C : Algorithm.CellCall) : Bool := by
  classical
  exact decide C.PathConsistent

/-- Step 4 of `sec:algorithm`: `Σ_{z ∈ Z_c} Q·V̂(z) = Σ_{z ∈ Z_c} Σ_j (pred · mask)(z, U_j, V_j)` over the samples of
the chosen seed. -/
noncomputable def acceptTotal (C : Algorithm.CellCall) : ℤ :=
  ∑ z ∈ C.certifiedColumns, ∑ j, Algorithm.CellCall.bitInt (C.pred z (C.samples j)) * C.pointMask z (C.samples j)

/-- Step 4 of `sec:algorithm`: `Σ_{z ∈ Z_c} Q·μ̂(z) = Σ_{z ∈ Z_c} Σ_j mask(z, U_j, V_j)` over the samples of the
chosen seed. -/
noncomputable def maskTotal (C : Algorithm.CellCall) : ℤ :=
  ∑ z ∈ C.certifiedColumns, ∑ j, C.pointMask z (C.samples j)

/-- The word of a stage: `true` followed by `payload` on a dispatched call, and `false` followed by the final
interval `outputWord (admittedValue … Builder.value c w)` on every other call. -/
noncomputable def stageWord (B1 B2 : ℕ) (payload : (c : Call) → Selected c → List Bool → List Bool)
    (c : Call) (w : List Bool) : List Bool :=
  match dispatch B1 B2 c with
  | some p => true :: payload c p w
  | none => false :: outputWord (admittedValue B1 B2 Builder.value c w)

/-- After `prep`: the call, its parameters and the witness prefix. -/
noncomputable def prepWord (B1 B2 : ℕ) : Call → List Bool → List Bool :=
  stageWord B1 B2 fun c p w => callWord c ++ parametersWord p.1 ++ frame (witnessPrefix c p.1 w)

/-- After `cert`: the data of `prepWord` and the certified columns `Z_c`. -/
noncomputable def certWord (B1 B2 : ℕ) : Call → List Bool → List Bool :=
  stageWord B1 B2 fun c p w => callWord c ++ parametersWord p.1 ++ frame (witnessPrefix c p.1 w) ++
    frame (certifiedBits (runCall c p w))

/-- After `greedy`: the data of `certWord`, path consistency and the chosen seed of Step 3. -/
noncomputable def greedyWord (B1 B2 : ℕ) : Call → List Bool → List Bool :=
  stageWord B1 B2 fun c p w => callWord c ++ parametersWord p.1 ++ frame (witnessPrefix c p.1 w) ++
    frame (certifiedBits (runCall c p w)) ++ bitWord (consistentBit (runCall c p w)) ++
    frame (runCall c p w).chosenSeed

/-- After `main`: exactly the inputs of Step 5 of `sec:algorithm`: `n`, `k`, `Q`, `M_F`, `η`, `n_c = |Z_c|`, path
consistency, and the two totals of Step 4. -/
noncomputable def mainWord (B1 B2 : ℕ) : Call → List Bool → List Bool :=
  stageWord B1 B2 fun c p w => natWord c.n ++ natWord p.1.k ++ natWord p.1.Q ++ natWord p.1.MF ++
    ratWord p.1.eta ++ natWord (runCall c p w).certifiedColumns.card ++ bitWord (consistentBit (runCall c p w)) ++
    NearCubicGates.Close.Interfaces.intWord (acceptTotal (runCall c p w)) ++
    NearCubicGates.Close.Interfaces.intWord (maskTotal (runCall c p w))

/-! ## Cost ledgers -/

/-- The three-term envelope of `prop:time`, `Machine.propTimeEnvelope`, at the parameters of a
dispatched call, and `0` on every other call. -/
noncomputable def runEnvelope (B1 B2 e : ℕ) (c : Call) : ℕ :=
  match dispatch B1 B2 c with
  | some p => Machine.propTimeEnvelope c.n p.1.k p.1.Q p.1.Jmax p.1.lambda e
  | none => 0

theorem runEnvelope_of_not_admitted {B1 B2 e : ℕ} {c : Call} (h : ¬ Transfer.Admitted4 B1 B2 c) :
    runEnvelope B1 B2 e c = 0 := by
  unfold runEnvelope
  rw [dispatch_of_not_admitted h]

/-- A polynomial cost in the length of the call word, for every witness (`prop:time`: parameter
preparation is polynomial). -/
def PolyCost (budget : Call → List Bool → ℕ) : Prop :=
  ∃ K e : ℕ, ∀ (c : Call) (w : List Bool), budget c w ≤ K * ((callWord c).length + 1) ^ e

/-- The cost ledger of a step of `prop:time`: polynomial in the call word, plus a constant times
the three-term envelope `2^{n-k} n^{2J_max+e} + 2^{n-k} Q n^e + 2^{10k+eλ}` on dispatched calls. -/
def LedgerCost (B1 B2 : ℕ) (budget : Call → List Bool → ℕ) : Prop :=
  ∃ K e : ℕ, ∀ (c : Call) (w : List Bool),
    budget c w ≤ K * ((callWord c).length + 1) ^ e + K * runEnvelope B1 B2 e c

/-! ## The machine components -/

/-- The request word of the counter: the call word and the witness word, each framed (`Transfer.Counter4`). -/
def requestWord (r : Call × List Bool) : List Bool := frame (callWord r.1) ++ frame r.2

/-- **The machine half of `thm:counter`, stage by stage** (`sec:algorithm`, paper/paper.tex, with
the costs of `prop:time`). Each field is a word function on (call, witness word) with its exact
output, or the cost bound of that word function:

* `prep` (`sec:params`, the witness): reads the call and the witness word and writes
  `prepWord`, i.e. the §9 parameters `Cells.prepare` and the witness prefix of a dispatched call, or the final
  interval of any other call (the sound default, or the exact value of a call with `W = 0`); polynomial time in
  the call word, whatever the witness;
* `cert` (Steps 1–2): writes the certified columns `Z_c` (`certWord`);
* `greedy` (Step 3): writes path consistency and the chosen seed (`greedyWord`);
* `main` (Step 4): writes the totals `Σ_{Z_c} Q V̂` and `Σ_{Z_c} Q μ̂` with the other inputs of
  Step 5 (`mainWord`);
* `output` (Step 5): writes `outputWord (p̂, κ̂)` for the value of the counter, in polynomial time
  (its exact arithmetic is `Program.dispatched_value`).

The four later stages pass the final interval of a call that is not dispatched on to the next stage. -/
structure MachineComponents (B1 B2 : ℕ) where
  /-- The cost of `prep`. -/
  prepBudget : Call → List Bool → ℕ
  /-- Parameter preparation and the witness prefix. -/
  prep : WordFunction (Call × List Bool) requestWord (fun r => frame (prepWord B1 B2 r.1 r.2))
    (fun r => prepBudget r.1 r.2)
  prepCost : PolyCost prepBudget
  /-- The cost of `cert`. -/
  certBudget : Call → List Bool → ℕ
  /-- Steps 1–2: incidences, structural mask, walk list, certification tables and `Z_c`. -/
  cert : WordFunction (Call × List Bool) (fun r => prepWord B1 B2 r.1 r.2)
    (fun r => frame (certWord B1 B2 r.1 r.2)) (fun r => certBudget r.1 r.2)
  certCost : LedgerCost B1 B2 certBudget
  /-- The cost of `greedy`. -/
  greedyBudget : Call → List Bool → ℕ
  /-- Step 3: seed fixing by the printed potentials `Ψ̃`. -/
  greedy : WordFunction (Call × List Bool) (fun r => certWord B1 B2 r.1 r.2)
    (fun r => frame (greedyWord B1 B2 r.1 r.2)) (fun r => greedyBudget r.1 r.2)
  greedyCost : LedgerCost B1 B2 greedyBudget
  /-- The cost of `main`. -/
  mainBudget : Call → List Bool → ℕ
  /-- Step 4: the main pass over the samples of the chosen seed. -/
  main : WordFunction (Call × List Bool) (fun r => greedyWord B1 B2 r.1 r.2)
    (fun r => frame (mainWord B1 B2 r.1 r.2)) (fun r => mainBudget r.1 r.2)
  mainCost : LedgerCost B1 B2 mainBudget
  /-- The cost of `output`. -/
  outputBudget : Call → List Bool → ℕ
  /-- Step 5: the outward-rounded interval. -/
  output : WordFunction (Call × List Bool) (fun r => mainWord B1 B2 r.1 r.2)
    (fun r => outputWord (admittedValue B1 B2 Builder.value r.1 r.2)) (fun r => outputBudget r.1 r.2)
  outputCost : PolyCost outputBudget

end NearQuarticWires.Program
