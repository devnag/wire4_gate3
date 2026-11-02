import Proof.Quartic.Cells.ParametersAlgorithm
import Proof.Quartic.Cells.ParametersSampler
import Proof.Quartic.Algorithm.Complete
import Proof.Quartic.Algorithm.Window
import Proof.Quartic.Transfer.Counter4
import Proof.Quartic.Mask.Structural
import Proof.Quartic.Cells.Score
import Proof.Quartic.Cells.Partition
import Proof.Wire_3_5.PrimTC4GeoV
import Proof.Wire_3_5.SeedFixSampler

/-!
# From a normalized call and a witness to the input of Steps 2–5

Paper: `sec:cells`, paper/paper.tex; `def:mask`; `sec:walks`;
the witness; `sec:params`.

For a call `c` whose parameters are selected by the exact rules of `sec:params` (`Cells.prepare`, with every rule
recorded in `Cells.ParameterRules`), and a witness word, `cellCall` is the input of Steps 2–5 of the counting
algorithm (`Algorithm.CellCall`):

* the partition of `imp:partition` is the star partition `Cells.ParameterRules.starParams` at the translation named
  by the witness's partition index; its `2^{n-k}` centers are the columns and its `N = 2^{k/2}` patterns per side
  index the rows and columns of a cell;
* `pred z (u, v) = pred(c(z) ⊕ u ⊕ v)`;
* the column data are the structural mask `smask` of `def:mask` (heavy coordinates with incidence at least `d^*`),
  `X(z,u,v) = Σ_{(j,i) ∈ 𝒮} |Δ_{j,i}(z,u,v)|`, the mixed residuals `R_j` of `sec:cells`, the proposed chain values
  `K^{(j)}_{r,σ}(z,w) = Σ_t ξ^{(j)}_{r,t} c_{j,t}(z,w,σ)` of `sec:walks`, and the constants `τ`, `X_max`, `a_r`,
  `M_1`, `A`, `h_E`, `Λ` of `sec:params`.

The index convention: `Walks.WalkData N m J` has digits indexed by `Fin (J + 1)` and the final error at index `J`,
so the cell call carries `J - 1` for the paper's `J` stages; the stored value at index `i` is `K_{i+1}`, and the
stored multiplier at index `i` is `a_{i+1}`, so that `Walks.WalkData.E` is the paper's
`E_0 = K_1`, `E_r = K_{r+1} - a_r K_r`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces

/-! ### The parameter input of a call -/

/-- The data of a call that the parameter rules of `sec:params` read (paper/paper.tex): the input
length `n`, the wire count `W = W(C¹) + W(C²)`, the occurrence counts `G_1`, `G_2`, the radius `β`, and whether the
call is a pair call. -/
def callInput (c : Call) : Cells.ParameterInput where
  n := c.n
  W := Transfer.callWires c
  G1 := c.first.gates.length
  G2 := c.second.gates.length
  beta := c.radius
  pair := decide (c.kind = .pair)

/-- The occurrence lists of the two circuits `C¹`, `C²` of a call (`sec:cells`). -/
def gatesOf (c : Call) : Fin 2 → List (NormalizedThresholdGate c.n) :=
  ![c.first.gates, c.second.gates]

/-- The occurrence counts `G_1`, `G_2` (`sec:cells`). -/
def occurrences (c : Call) : Fin 2 → ℕ := fun j => (gatesOf c j).length

/-- All occurrences of the call, those of `C¹` followed by those of `C²`; their labels are the positions in this
list, so repeated gates remain distinct (`def:mask`). -/
def allGates (c : Call) : List (NormalizedThresholdGate c.n) := c.first.gates ++ c.second.gates

/-- The set `𝒥` of circuits of the call, as indices `0 ↦ C¹`, `1 ↦ C²` (`sec:cells`):
`𝒥 = {1, 2}` for pair calls and `𝒥 = {1}` otherwise. -/
def circuitSet (c : Call) : Finset (Fin 2) := if decide (c.kind = .pair) then {0, 1} else {0}

section Build

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p)

/-- The star partition of `imp:partition` selected by the parameters, on the call's `n` inputs. -/
abbrev star : StarParams := hs.starParams

/-- The cell side `N = 2^{k/2}` is `2^{s r/2}`, the number of mixed-radix pattern codes. -/
theorem seedN_eq_patternCodes :
    hs.seedParameters.N = 2 ^ NearCubicWires.WireExponent3_5.SeedFix.callKh (star c hs) := by
  show 2 ^ (p.k / 2) = 2 ^ ((star c hs).s * (p.r / 2))
  rw [Cells.ParameterRules.star_s hs, hs.k_eq]
  obtain ⟨m, hm⟩ := (Cells.ParameterRules.r_even_large hs).1
  congr 1
  rw [hm, show (m + m) * p.s = 2 * (m * p.s) by ring, show (m + m) / 2 = m by omega,
    Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_comm]

/-- The `N = 2^{k/2}` patterns of one side of a cell, indexed by `Fin N` (`imp:partition`), in the
mixed-radix order of their block choices, lowest block first (`SeedFix.callEqv`). -/
def patternEquiv : Fin hs.seedParameters.N ≃ (star c hs).Errors :=
  (finCongr (seedN_eq_patternCodes c hs)).trans (NearCubicWires.WireExponent3_5.SeedFix.callEqv (star c hs)).symm

/-- A translation is `r` syndromes of `s` bits; its code is the base-`2^s` number of the syndromes, lowest block
first, each syndrome a base-two number, lowest bit first. -/
def translationCode (P : StarParams) : P.Translation ≃ Fin ((2 ^ P.s) ^ P.r) :=
  (Equiv.piCongrRight fun _ => finFunctionFinEquiv).trans finFunctionFinEquiv

theorem translationCount_eq : 2 ^ p.k = (2 ^ (star c hs).s) ^ (star c hs).r := by
  rw [← pow_mul, Cells.ParameterRules.star_s hs, hs.k_eq, Nat.mul_comm]
  rfl

/-- The `2^k` partitions of `imp:partition`, indexed by the witness's partition index in the order of
`translationCode`. -/
def translationEquiv : Fin (2 ^ p.k) ≃ (star c hs).Translation :=
  (finCongr (translationCount_eq c hs)).trans (translationCode (star c hs)).symm

/-- The number of free center bits splits into the left and right halves of `imp:partition`. -/
theorem centerCount_eq :
    c.n - p.k = NearCubicWires.WireExponent3_5.PrimT.C4Geo.dRow (star c hs) +
      NearCubicWires.WireExponent3_5.PrimT.C4Geo.dR (star c hs) := by
  have h := (star c hs).centerBits_sum
  rw [Cells.ParameterRules.star_k hs] at h
  exact h.symm

/-- **The center of column `z`** of the partition `σ`: the table point `C4Geo.centerAt` at the row given by the low
`d_L` bits of `z` and the column given by its high `d_R` bits. It is the offset of `σ` (a point of the coset in every
block) plus the shared linear map of the star: the repeated Hamming-code generator on the blocks and identity
columns on the unblocked coordinates, the left half read from the row and the right half from the column. -/
def centerOf (σ : (star c hs).Translation) (z : ℕ) : BitInput c.n :=
  NearCubicWires.WireExponent3_5.PrimT.C4Geo.centerAt (star c hs) σ
    (z % 2 ^ NearCubicWires.WireExponent3_5.PrimT.C4Geo.dRow (star c hs))
    (z / 2 ^ NearCubicWires.WireExponent3_5.PrimT.C4Geo.dRow (star c hs))

theorem centerOf_isCenter (σ : (star c hs).Translation) (z : ℕ) : (star c hs).IsCenter σ (centerOf c hs σ z) :=
  NearCubicWires.WireExponent3_5.PrimT.C4Geo.centerAt_isCenter _ σ _ _

theorem centerOf_injective (σ : (star c hs).Translation) :
    Function.Injective fun z : Fin (2 ^ (c.n - p.k)) =>
      (⟨centerOf c hs σ z, centerOf_isCenter c hs σ z⟩ : {x // (star c hs).IsCenter σ x}) := by
  intro z z' h
  have h' := congrArg Subtype.val h
  set dL := NearCubicWires.WireExponent3_5.PrimT.C4Geo.dRow (star c hs)
  set dR := NearCubicWires.WireExponent3_5.PrimT.C4Geo.dR (star c hs)
  have hcount := centerCount_eq c hs
  have hpos : 0 < 2 ^ dL := Nat.two_pow_pos _
  have hlt : ∀ y : Fin (2 ^ (c.n - p.k)), (y : ℕ) / 2 ^ dL < 2 ^ dR := by
    intro y
    rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add, Nat.add_comm, ← hcount]
    exact y.isLt
  obtain ⟨h1, h2⟩ := NearCubicWires.WireExponent3_5.PrimT.C4Geo.centerAt_inj (star c hs) σ _ _ _ _
    (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) (hlt z) (hlt z') h'
  apply Fin.ext
  rw [← Nat.mod_add_div (z : ℕ) (2 ^ dL), ← Nat.mod_add_div (z' : ℕ) (2 ^ dL), h1, h2]

/-- The `2^{n-k}` centers of a partition, indexed as the columns `Fin n_col` (`imp:partition`), by
`centerOf`. -/
noncomputable def centerEquiv (σ : (star c hs).Translation) :
    Fin (2 ^ (c.n - p.k)) ≃ {x // (star c hs).IsCenter σ x} :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨centerOf_injective c hs σ, by rw [Fintype.card_fin, Cells.ParameterRules.centers_card hs σ]; rfl⟩)

theorem centerEquiv_apply (σ : (star c hs).Translation) (z : Fin (2 ^ (c.n - p.k))) :
    (centerEquiv c hs σ z).val = centerOf c hs σ z := rfl

/-- The parameters of `sec:params` in the notation of the counting algorithm (`Cells.toAlgorithmParameters`). -/
noncomputable abbrev algorithmParameters : Algorithm.Parameters :=
  Cells.toAlgorithmParameters (callInput c) p hs

/-- The witness of `sec:algorithm` (paper/paper.tex) read from a binary word, with the paper's `k`,
`J` and occurrence counts. -/
def witness (w : List Bool) : Algorithm.Witness p.k p.J (occurrences c) :=
  Algorithm.decodeWitness p.k p.J (occurrences c) w

/-- (W2) of the witness, `sec:algorithm`, paper/paper.tex: the set `𝒮` as one bit per occurrence label, in the order of
`allGates` (the bit at position `k + i`, as in `Algorithm.decodeWitness`). -/
def selection (w : List Bool) (i : Fin (allGates c).length) : Bool :=
  Algorithm.witnessBit w (p.k + i)

/-- (W1) of the witness: the partition of `imp:partition` named by the partition index. -/
def translation (w : List Bool) : (star c hs).Translation :=
  translationEquiv c hs (witness c (p := p) w).partitionIndex

/-- The center `c(z)` of column `z` in the partition named by the witness. -/
def center (w : List Bool) (z : Fin (2 ^ (c.n - p.k))) : BitInput c.n :=
  centerOf c hs (translation c hs w) z

/-- The center of column `z` is the table point `centerOf` of the partition named by the witness. -/
theorem center_eq_centerOf (w : List Bool) (z : Fin (2 ^ (c.n - p.k))) :
    center c hs w z = centerOf c hs (translation c hs w) z := rfl

/-- The pattern of a row or column index of a cell. -/
def pattern (i : Fin hs.seedParameters.N) : (star c hs).Errors := patternEquiv c hs i

/-- (W3) of the witness, `sec:algorithm`, paper/paper.tex: the bit `ξ^{(j)}_{i+1,t}` as an integer, for the
stored index `i < J` (zero beyond `J`). -/
def chainBit (w : List Bool) (j : Fin 2) (i : ℕ) (t : Fin (occurrences c j)) : ℤ :=
  if h : i < p.J then Algorithm.CellCall.bitInt ((witness c (p := p) w).vectors j ⟨i, h⟩ t) else 0

/-- `sec:walks`, paper/paper.tex: the contribution
`c_{j,t}(z,w,σ) = Σ_l σ_l Δ_{j,t}(z, e_l)` of occurrence `t` of circuit `j` along the walk `w`. -/
noncomputable def contribution (w : List Bool) (z : Fin (2 ^ (c.n - p.k))) (j : Fin 2)
    (t : Fin (occurrences c j)) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder) : ℤ :=
  ∑ l, Cycle.signValue (σ l) *
    Cells.delta (star c hs) ((gatesOf c j)[(t : ℕ)]'t.isLt) (center c hs w z)
      (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).1)
      (pattern c hs (Cycle.edge Algorithm.traceOrder_pos walk l).2)

/-- The column data of `sec:walks` and `def:mask` for column `z` (paper/paper.tex):
the structural mask, `τ`, `X_max`, `X`, `𝒥`, the residuals `R_j`, the proposed values `K^{(j)}_{i+1,σ}`, the
multipliers `a_{i+1}`, `M_1`, `A`, `h_E` and `Λ`. -/
noncomputable def columnData (w : List Bool) (z : Fin (2 ^ (c.n - p.k))) :
    Walks.WalkData hs.seedParameters.N Algorithm.traceOrder (p.J - 1) where
  structural q := Mask.structuralMask ((star c hs).flipSet (star c hs).leftBlock)
    ((star c hs).flipSet (star c hs).rightBlock)
    (Mask.heavyCoordinates (Cells.incidence (allGates c)) p.dstar) (pattern c hs q.1) (pattern c hs q.2)
  tau := p.tau
  Xmax := p.Xmax
  X q := ∑ i : Fin (allGates c).length, if selection c (p := p) w i then
    (Cells.delta (star c hs) ((allGates c)[(i : ℕ)]'i.isLt) (center c hs w z) (pattern c hs q.1)
      (pattern c hs q.2)).natAbs else 0
  circuits := circuitSet c
  residual j q := Cells.residual (star c hs) (gatesOf c j) (center c hs w z) (pattern c hs q.1) (pattern c hs q.2)
  values j σ walk i := ∑ t : Fin (occurrences c j), chainBit c (p := p) w j i t * contribution c hs w z j t σ walk
  rate i := ((algorithmParameters c hs).rate i : ℤ)
  M := p.M1
  A := p.A
  hE := p.hE
  Lambda := p.Lambda

/-- **The input of Steps 2–5** for the call `c`, the selected parameters and the witness word `w`
(`sec:algorithm`, paper/paper.tex). -/
noncomputable def cellCall (w : List Bool) : Algorithm.CellCall where
  n := c.n
  ncol := 2 ^ (c.n - p.k)
  seed := hs.seedParameters
  J := p.J - 1
  k := p.k
  G := occurrences c
  MF := p.MF
  η := p.eta
  primes := p.primes
  e := p.e
  pred z q := c.predicate ((star c hs).point (center c hs w z) (pattern c hs q.1) (pattern c hs q.2))
  column := columnData c hs w

end Build

end NearQuarticWires.Builder
