import Proof.Quartic.Walks.Certification
import Proof.Quartic.Walks.Residue
import Proof.Quartic.Cycle.ConditionalIdentity

/-!
# The counting algorithm of `sec:algorithm` as an exact mathematical function

Paper: `sec:algorithm`, paper/paper.tex (the witness, Steps 1–5), with the objects of
`sec:walks` and `sec:printing`.

The algorithm is defined here without a clock: every step is an exact function over `ℚ`, `ℤ` and finite sets.
Its input is a `CellCall`: one normalized call on the cells of the partition named by the witness, together with the
witness's set `𝒮` and vectors `ξ` (through the per-column data `Walks.WalkData`), and the parameters of `sec:params`
that Steps 2–5 read. The steps are:

* **Step 2.** A column is *certified* when the three strict moment tests `eq:testX`, `eq:testE`, `eq:testPhi`
  pass (`Walks.ColumnCertificate`, paper/paper.tex).
* **Step 3.** Seed fixing. For a seed prefix `π`, the printed residue counts `Π` of `lem:residue` are decoded to
  `𝒩` by the centred residue modulo `p^e`, the exact system on the box `Bx(δ)` is solved over `ℚ`, and the values
  `v_{z,σ,δ} = H̃(0)` are summed with the weights `κ_σ` into `Ψ̃(π)` (paper/paper.tex). Each of the `S` rounds
  appends the bit whose child has the smaller `Ψ̃`, with ties going to `0`.
* **Step 4.** The main pass: the sampled means `V̂(z)` and `μ̂(z)` over the final sample list.
* **Step 5.** The interval `[Lo, Hi]`, rounded outward to multiples of `2^{-n}`, and `(p̂, κ̂)`.

If some reconstruction system met along the seed path is inconsistent, the algorithm returns the sound default
`(1/2, 1/2)`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Algorithm

open Finset
open NearQuarticWires.Sampler (Cell)

/-- The trace order `m = 4` fixed in `sec:fourier`, paper/paper.tex. -/
abbrev traceOrder : ℕ := 4

theorem traceOrder_pos : 0 < traceOrder := by norm_num

/-- The input of Steps 2–5 of `sec:algorithm` (paper/paper.tex): one normalized call on the cells
of the partition chosen by the witness, with the witness's `𝒮` and `ξ` already inside the column data.

* `n` is the input length; `ncol = 2^{n-k}` is the number of columns.
* `seed` fixes `N = 2^{k/2}`, the number `Q` of samples and the field degree `ℓ_f` of `imp:seed`; the seed length is
  `S = 2mℓ_f = 8ℓ_f` (`Cycle.seedLength`).
* `pred z (u, v)` is `pred(c(z) ⊕ u ⊕ v)`.
* `column z` holds the structural mask `smask`, `τ`, `X_max`, `X(z, ·)`, the set `𝒥` of circuits, the mixed
  residuals `R_j(z, ·)`, the proposed chain values `K^{(j)}_{r,σ}(z, w)`, the chain `a_r`, `M_1`, `A`, and `h_E`, `Λ`.
* `k` is the exponent of the moment tests; `G j` is the number of occurrences of circuit `j`.
* `MF`, `η`, `primes = 𝒫` and `e` are the parameters of `sec:params` items 4 and 6. -/
structure CellCall where
  n : ℕ
  ncol : ℕ
  seed : Cycle.SeedParameters
  J : ℕ
  k : ℕ
  G : Fin 2 → ℕ
  MF : ℕ
  η : ℚ
  primes : Finset ℕ
  e : ℕ
  pred : Fin ncol → Cell seed.N → Bool
  column : Fin ncol → Walks.WalkData seed.N traceOrder J

/-- Step 3, `sec:algorithm`, paper/paper.tex: one round appends the bit whose child has the smaller `Ψ̃`; on ties
the bit is `0` (`false`). -/
def greedyStep (Ψ : List Bool → ℚ) (π : List Bool) : List Bool :=
  π ++ [decide (Ψ (π ++ [true]) < Ψ (π ++ [false]))]

/-- Step 3, `sec:algorithm`, paper/paper.tex: the `S` greedy rounds from the empty prefix, for an arbitrary
objective `Ψ`. -/
def greedySeed (S : ℕ) (Ψ : List Bool → ℚ) : List Bool := (greedyStep Ψ)^[S] []

namespace CellCall

variable (C : CellCall)

/-- The value `1` or `0` of a bit, as an integer. -/
def bitInt (b : Bool) : ℤ := if b then 1 else 0

/-- `def:mask`, paper/paper.tex: the mask `mask(z,u,v) = smask(u,v) · 1[X(z,u,v) ≤ τ]` of column
`z` at the point `c`, as an integer bit. -/
def pointMask (z : Fin C.ncol) (c : Cell C.seed.N) : ℤ :=
  Mask.mask ((C.column z).structural c) (C.column z).tau ((C.column z).X c)

/-- Step 2, paper/paper.tex: column `z` is *certified* when the strict tests `eq:testX`,
`eq:testE` and `eq:testPhi` pass. -/
def Certified (z : Fin C.ncol) : Prop :=
  Walks.ColumnCertificate traceOrder_pos C.k (C.column z)

/-- Step 2, `sec:algorithm`, paper/paper.tex: the set `Z_c` of certified columns. -/
noncomputable def certifiedColumns : Finset (Fin C.ncol) := by
  classical
  exact Finset.univ.filter C.Certified

/-! ### Step 3: seed fixing -/

/-- The seed length `S = 2mℓ_f` (`imp:seed`, paper/paper.tex). -/
def seedLength : ℕ := Cycle.seedLength C.seed

/-- The number whose binary digits, lowest first, are the bits of a seed prefix. Its low `|π|` bits are the prefix
of `imp:seed` (`Cycle.conditionalGamma` reads prefixes in this form). -/
def prefixValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * prefixValue bs

/-- `cor:conditional`, paper/paper.tex: the integer walk weight `2^S c_π(w)` of a prefix `π`. -/
noncomputable def walkWeight (π : List Bool) (w : Cycle.Walk C.seed.N traceOrder) : ℤ :=
  Cycle.scaledGamma C.seed π.length (prefixValue π) w

/-- `sec:printing`, paper/paper.tex: the integer linear forms whose residues `Π` counts, for one
pattern `σ`: the digits `E^{(j)}_{r,σ}` (index `some r`) and the walk sum `Y_{j,σ}` (index `none`) of each circuit
`j ∈ 𝒥`. Circuits outside `𝒥` contribute the zero form. -/
def residueForms (z : Fin C.ncol) (σ : Cycle.SignPattern traceOrder) (w : Cycle.Walk C.seed.N traceOrder) :
    Fin 2 × Option (Fin (C.J + 1)) → ℤ := fun f =>
  if f.1 ∈ (C.column z).circuits then
    match f.2 with
    | some r => (C.column z).E f.1 σ w r
    | none => (C.column z).Y traceOrder_pos f.1 σ w
  else 0

/-- `sec:printing`, paper/paper.tex: the residue vector `(ρ_E, ρ_Y)` with `ρ_E = δ mod p`. -/
def residueTarget (z : Fin C.ncol) (p : ℕ) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (ρY : Fin 2 → ℤ) :
    Fin 2 × Option (Fin (C.J + 1)) → ℤ := fun f =>
  if f.1 ∈ (C.column z).circuits then
    match f.2 with
    | some r => δ f.1 r % (p : ℤ)
    | none => ρY f.1
  else 0

/-- `lem:residue`, paper/paper.tex: the printed integer `Π(z)` for the prefix `π`, the pattern `σ`,
the prime `p` and the residue vector `(δ mod p, ρ_Y)`. The sum runs over all closed walks; the walks outside `W_s`
contribute zero because the mask polynomial carries the factor `smask` on every edge. -/
noncomputable def printedCount (π : List Bool) (z : Fin C.ncol) (σ : Cycle.SignPattern traceOrder) (p : ℕ)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) (ρY : Fin 2 → ℤ) : ℤ :=
  Walks.residuePolynomial (C.walkWeight π)
    (Walks.walkMaskPoly traceOrder_pos (C.column z).structural (C.column z).tau (C.column z).Xmax
      (C.column z).X)
    p C.e (C.residueForms z σ) (C.residueTarget z p δ ρY)

/-- `lem:residue`, paper/paper.tex and Step 3: the recovered count `𝒩(z)`, the
centred representative of `Π(z)` modulo `p^e`. -/
noncomputable def recoveredCount (π : List Bool) (z : Fin C.ncol) (σ : Cycle.SignPattern traceOrder) (p : ℕ)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) (ρY : Fin 2 → ℤ) : ℤ :=
  Walks.centeredResidue ((p : ℤ) ^ C.e) (C.printedCount π z σ p δ ρY)

/-- Step 3, `sec:algorithm`, paper/paper.tex: the digit vectors `δ = (δ^{(j)})_{j ∈ 𝒥}` with entries in
`(-h_E, h_E)`; circuits outside `𝒥` carry the zero vector. -/
noncomputable def digitVectors (z : Fin C.ncol) : Finset (Fin 2 → Fin (C.J + 1) → ℤ) := by
  classical
  exact Fintype.piFinset fun j =>
    if j ∈ (C.column z).circuits then
      Fintype.piFinset fun _ => Finset.Ioo (-((C.column z).hE : ℤ)) (C.column z).hE
    else {0}

/-- `lem:certify`(d), paper/paper.tex and Step 3: the box
`Bx(δ) = ∏_{j ∈ 𝒥} Bx_j(δ^{(j)})`, with `Bx_j(δ) = [⌈(M_1K(δ)-Λ+1)/A⌉, ⌊(M_1K(δ)+Λ-1)/A⌋] ∩ [-2mG_j, 2mG_j]`;
the coordinate of a circuit outside `𝒥` is fixed to `0`. -/
noncomputable def box (z : Fin C.ncol) (δ : Fin 2 → Fin (C.J + 1) → ℤ) : Finset (Fin 2 → ℤ) := by
  classical
  exact Fintype.piFinset fun j =>
    if j ∈ (C.column z).circuits then
      Walks.fullBox ((C.column z).M * Walks.digitValue (C.column z).rate (δ j)) (C.column z).A
        (C.column z).Lambda ((2 * traceOrder : ℕ) * (C.G j : ℤ))
    else {0}

/-- Step 3, `sec:algorithm`, paper/paper.tex: the residue vectors `ρ_Y ∈ (ℤ/p)^{𝒥}`, as representatives in
`[0, p)`; circuits outside `𝒥` carry `0`. -/
noncomputable def residueVectors (z : Fin C.ncol) (p : ℕ) : Finset (Fin 2 → ℤ) := by
  classical
  exact Fintype.piFinset fun j =>
    if j ∈ (C.column z).circuits then Finset.Ico (0 : ℤ) p else {0}

/-- Step 3, paper/paper.tex (with `imp:window`): `H` *solves the system* of
column `z`, pattern `σ` and digit vector `δ` at the prefix `π` when it is supported on `Bx(δ)` and its push-forward
modulo every `p ∈ 𝒫` equals the recovered count: `H_p(ρ_Y) = 𝒩(z)` at `(ρ_E, ρ_Y) = (δ mod p, ρ_Y)`. -/
def Solves (π : List Bool) (z : Fin C.ncol) (σ : Cycle.SignPattern traceOrder)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) (H : (Fin 2 → ℤ) → ℚ) : Prop :=
  (∀ y, y ∉ C.box z δ → H y = 0) ∧
    ∀ p ∈ C.primes, ∀ ρY ∈ C.residueVectors z p,
      (∑ y ∈ (C.box z δ).filter (fun y => ∀ j, y j ≡ ρY j [ZMOD (p : ℤ)]), H y) =
        (C.recoveredCount π z σ p δ ρY : ℚ)

/-- Step 3, `sec:algorithm`, paper/paper.tex: `v_{z,σ,δ} = H̃(0)` for the exact solution `H̃` of the system (which is
supported on `Bx(δ)`, so `H̃(0) = 0` when `0 ∉ Bx(δ)`); an inconsistent system is reported separately. -/
noncomputable def reconstructedValue (π : List Bool) (z : Fin C.ncol) (σ : Cycle.SignPattern traceOrder)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) : ℚ := by
  classical
  exact if h : ∃ H, C.Solves π z σ δ H then Classical.choose h 0 else 0

/-- Step 3, `sec:algorithm`, paper/paper.tex: `Ψ̃(π) = Σ_{z ∈ Z_c} Σ_σ κ_σ Σ_δ v_{z,σ,δ}`. -/
noncomputable def printedPotential (π : List Bool) : ℚ :=
  ∑ z ∈ C.certifiedColumns, ∑ σ : Cycle.SignPattern traceOrder,
    (Cycle.kappa traceOrder σ : ℚ) * ∑ δ ∈ C.digitVectors z, C.reconstructedValue π z σ δ

/-- Step 3, `sec:algorithm`, paper/paper.tex: the seed chosen by the algorithm. -/
noncomputable def chosenSeed : List Bool := greedySeed C.seedLength C.printedPotential

/-- Step 3, `sec:algorithm`, paper/paper.tex: every system met on the seed path is consistent: for both children of
every prefix of the chosen seed, every certified column, every `σ` with `κ_σ ≠ 0` and every digit vector. -/
def PathConsistent : Prop :=
  ∀ i < C.seedLength, ∀ b : Bool, ∀ z ∈ C.certifiedColumns, ∀ σ : Cycle.SignPattern traceOrder,
    Cycle.kappa traceOrder σ ≠ 0 → ∀ δ ∈ C.digitVectors z,
      ∃ H, C.Solves (C.chosenSeed.take i ++ [b]) z σ δ H

/-! ### Step 4: the main pass -/

/-- Step 4, `sec:algorithm`, paper/paper.tex: the sample list `(U_j, V_j)` of the final seed. -/
noncomputable def samples : Fin C.seed.Q → Cell C.seed.N :=
  Cycle.seedSample C.seed (prefixValue C.chosenSeed)

/-- Step 4, `sec:algorithm`, paper/paper.tex: `V̂(z) = Q^{-1} Σ_j (pred · mask)(z, U_j, V_j)` for a sample list. -/
def sampledAccept (S : Fin C.seed.Q → Cell C.seed.N) (z : Fin C.ncol) : ℚ :=
  (∑ j, (bitInt (C.pred z (S j)) * C.pointMask z (S j) : ℤ) : ℚ) / C.seed.Q

/-- Step 4, `sec:algorithm`, paper/paper.tex: `μ̂(z) = Q^{-1} Σ_j mask(z, U_j, V_j)` for a sample list. -/
def sampledMask (S : Fin C.seed.Q → Cell C.seed.N) (z : Fin C.ncol) : ℚ :=
  (∑ j, C.pointMask z (S j) : ℤ) / C.seed.Q

/-! ### Step 5: output -/

/-- Step 5, `sec:algorithm`, paper/paper.tex: `Lo = n_col^{-1}[Σ_{z ∈ Z_c} V̂(z) - 2M_F n_c η]` for a set `Z` of
certified columns and a sample list. -/
def lower (Z : Finset (Fin C.ncol)) (S : Fin C.seed.Q → Cell C.seed.N) : ℚ :=
  ((∑ z ∈ Z, C.sampledAccept S z) - 2 * C.MF * Z.card * C.η) / C.ncol

/-- Step 5, `sec:analysis`, paper/paper.tex:
`Hi = n_col^{-1}[Σ_{z ∈ Z_c}(V̂(z) + 1 - μ̂(z)) + (2M_F+1) n_c η + (n_col - n_c)]`. -/
def upper (Z : Finset (Fin C.ncol)) (S : Fin C.seed.Q → Cell C.seed.N) : ℚ :=
  ((∑ z ∈ Z, (C.sampledAccept S z + 1 - C.sampledMask S z)) + (2 * C.MF + 1) * Z.card * C.η +
    ((C.ncol : ℚ) - Z.card)) / C.ncol

end CellCall

/-- Step 5, `prop:sound`, paper/paper.tex: round down to a multiple of `2^{-n}`. -/
def dyadicFloor (n : ℕ) (q : ℚ) : ℚ := (⌊q * 2 ^ n⌋ : ℤ) / (2 : ℚ) ^ n

/-- Step 5, `prop:sound`, paper/paper.tex: round up to a multiple of `2^{-n}`. -/
def dyadicCeil (n : ℕ) (q : ℚ) : ℚ := (⌈q * 2 ^ n⌉ : ℤ) / (2 : ℚ) ^ n

/-- Step 5, `prop:sound`, paper/paper.tex: `p̂ = (Lo + Hi)/2` and `κ̂ = (Hi - Lo)/2`, computed from the
outward-rounded endpoints. -/
def centerRadius (n : ℕ) (lo hi : ℚ) : ℚ × ℚ :=
  ((dyadicFloor n lo + dyadicCeil n hi) / 2, (dyadicCeil n hi - dyadicFloor n lo) / 2)

/-- `sec:params`, paper/paper.tex: the sound default `(p̂, κ̂) = (1/2, 1/2)`. -/
def soundDefault : ℚ × ℚ := (1 / 2, 1 / 2)

namespace CellCall

variable (C : CellCall)

/-- **The counting algorithm** of `sec:algorithm` on one cell call (paper/paper.tex): the sound
default if a system on the seed path is inconsistent, and otherwise `(p̂, κ̂)` from the rounded `Lo`, `Hi` of the
certified columns and the greedily fixed seed. -/
noncomputable def run : ℚ × ℚ := by
  classical
  exact if C.PathConsistent then
      centerRadius C.n (C.lower C.certifiedColumns C.samples) (C.upper C.certifiedColumns C.samples)
    else soundDefault

end CellCall

end NearQuarticWires.Algorithm
