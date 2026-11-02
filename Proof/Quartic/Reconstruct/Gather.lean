import Proof.Quartic.Reconstruct.Phases

/-!
# The listed systems from the call parameters and the printed tables

Paper: Step 3 of `sec:algorithm`, paper/paper.tex; `lem:certify`(d).

This file states what the gathering stage (`ReconstructPhases.systems`) computes, in terms of the data it reads:

* the points of a listed system depend only on the digit vector `δ` and the call parameters `M_1`, `A`, `Λ`, the rates,
  the occurrence counts `G_j` and the circuits `𝒥` (`boxAxisOf`, `boxAxis_eq`);
* its rows are, for the primes `p ∈ 𝒫` (increasing) and the residue vectors `ρ_Y` modulo `p`, the triples
  `(p, ρ_Y, 𝒩(z))` where `𝒩(z)` is entry `z` of the table printed for `(s, σ, p, δ, ρ_Y)` (`systemAt_rows`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

section Gather

variable (q : ChildRequest B1 B2)

/-- The coordinate `j` of the box `Bx(δ)` (`lem:certify`(d)) from the call parameters:
`[⌈(M_1K(δ^{(j)}) - Λ + 1)/A⌉, ⌊(M_1K(δ^{(j)}) + Λ - 1)/A⌋] ∩ [-2mG_j, 2mG_j]` for a circuit `j ∈ 𝒥`, `[0]`
otherwise. -/
noncomputable def boxAxisOf (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) (j : Fin 2) : List ℤ :=
  if j ∈ Builder.circuitSet q.call then
    intervalList
      (max (NearCubicGates.ScoreBox.lower ((q.selected.1.M1 : ℤ) * Walks.digitValue
          (fun i => ((Builder.algorithmParameters q.call (rules q)).rate i : ℤ)) (δ j))
        (q.selected.1.A : ℤ) 0 (q.selected.1.Lambda : ℤ)) (-(((2 * Algorithm.traceOrder : ℕ) : ℤ) *
          (Builder.occurrences q.call j : ℤ))))
      (min (NearCubicGates.ScoreBox.upper ((q.selected.1.M1 : ℤ) * Walks.digitValue
          (fun i => ((Builder.algorithmParameters q.call (rules q)).rate i : ℤ)) (δ j))
        (q.selected.1.A : ℤ) 0 (q.selected.1.Lambda : ℤ)) (((2 * Algorithm.traceOrder : ℕ) : ℤ) *
          (Builder.occurrences q.call j : ℤ)))
  else [0]

/-- The box of every column is computed from the call parameters. -/
theorem boxAxis_eq (z : Fin q.cellCall.ncol) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) (j : Fin 2) :
    boxAxis q.cellCall z δ j = boxAxisOf q δ j := rfl

/-- Entry `z` of a printed table is the recovered count `𝒩(z)`. -/
theorem printTable_getD (r : PrintRequest B1 B2) (z : Fin r.child.cellCall.ncol) :
    (printTable r).getD z.val 0 = recoveredCountOf r.child.cellCall
      (splitWeight r.child.cellCall r.child.seedPrefix r.sign) z r.pattern r.prime r.digits r.residues := by
  simp [printTable]

/-- The residue vectors of a column are those of the call. -/
theorem residueList_eq (z : Fin q.cellCall.ncol) (p : ℕ) : residueList q.cellCall z p = residueListOf q p := rfl

/-- The table printed for the part, the pattern and the digit vector of a system, at the prime `p` and the residue
vector `ρ_Y`. -/
noncomputable def tableOf (x : SystemIndex q) (p : ℕ) (hp : p ∈ q.cellCall.primes) (ρ : Fin 2 → ℤ) :
    PrintRequest B1 B2 where
  child := q
  sign := x.1
  pattern := x.2.1
  prime := p
  prime_mem := hp
  digits := x.2.2.1
  residues := ρ

/-- **The rows of a listed system from the printed tables** (Step 3 of `sec:algorithm`): for the primes `p ∈ 𝒫`
(increasing) and the residue vectors `ρ_Y` modulo `p`, the triple `(p, ρ_Y, 𝒩(z))`, where `𝒩(z)` is entry `z` of
the table printed for `(s, σ, p, δ, ρ_Y)`. -/
theorem systemAt_rows (x : SystemIndex q) :
    (systemAt q x).rows = (primeList q.cellCall).attach.flatMap fun p => (residueListOf q p.1).map fun ρ =>
      (p.1, [(ρ 0).toNat, (ρ 1).toNat],
        ((printTable (tableOf q x p.1 ((mem_primeList _ _).mp p.2) ρ)).getD x.2.2.2.val 0).toNat) := by
  show systemRows q.cellCall _ x.2.2.2 x.2.1 x.2.2.1 = _
  unfold systemRows
  conv_lhs => rw [← List.attach_map_subtype_val (primeList q.cellCall), List.flatMap_map]
  refine List.flatMap_congr fun p _ => ?_
  rw [residueList_eq]
  refine List.map_congr_left fun ρ _ => ?_
  rw [printTable_getD (tableOf q x p.1 ((mem_primeList _ _).mp p.2) ρ) x.2.2.2]
  rfl

end Gather

/-! ## The modulus of a printed table -/

/-- The prime of every print request is prime (`sec:params`, paper/paper.tex). -/
theorem PrintRequest.prime_prime (r : PrintRequest B1 B2) : r.prime.Prime :=
  (reconstructionHypotheses_of_dispatch r.child.dispatched r.child.witness).prime r.prime r.prime_mem

/-- The modulus `p^e` of every print request is at least `2` (`lem:residue`, paper/paper.tex). -/
theorem PrintRequest.two_le_modulus (r : PrintRequest B1 B2) : 2 ≤ r.prime ^ r.child.cellCall.e := by
  have he := (reconstructionHypotheses_of_dispatch r.child.dispatched r.child.witness).e_pos
  calc 2 ≤ r.prime := (PrintRequest.prime_prime r).two_le
    _ = r.prime ^ 1 := (pow_one _).symm
    _ ≤ r.prime ^ r.child.cellCall.e := Nat.pow_le_pow_right (PrintRequest.prime_prime r).pos he

end NearQuarticWires.Reconstruct
