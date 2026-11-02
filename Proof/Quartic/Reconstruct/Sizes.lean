import Proof.Quartic.Reconstruct.Schedule
import Proof.Quartic.Cells.ParametersWordBounds
import Proof.Quartic.Cells.ParametersScalarBounds

/-!
# The sizes of the requests of the reconstruction stage

Paper: `prop:time`, paper/paper.tex (every table index and every exact system has polynomial size),
with the parameter bounds of `sec:params` (`sec:params`, `Cells.ScalarPreparationBounds`).

The costs of one printed table and of one exact system are polynomial in the sizes of their requests
(`Greedy.ReconstructControl`: the bounds `printBound` and `solveBound` apply to index words and systems of length at
most `(n+1)^{e₀}`). This file gives one exponent `e₀`, depending only on `B₁`, such that on every child evaluation

* the index word `printIndexWord r` of every table the stage prints has length at most `(n+1)^{e₀}`
  (`printIndexWord_length_le`), and
* the word `sysWord` of every listed system `systemOf` has length at most `(n+1)^{e₀}` (`sysWord_length_le`).

All parameters that enter (`P`, `h_E`, `J`, `e`, `G_1`, `G_2`) are at most the preparation envelope
`V = preparationEnvelope B₁ n`, a polynomial in `n`; the recovered counts are below `p^e ≤ 2^{Pe}`, and the box
coordinates lie in `[-2mG_j, 2mG_j]`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open Finset
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearCubicGates.Close.Interfaces.Formats (SysReq SolveMachine)

variable {B1 B2 : ℕ}

/-! ## Lengths of the codes -/

theorem natWord_length_le_self (v : ℕ) : (natWord v).length ≤ 2 * v + 3 :=
  Cells.ParameterArithmetic.natWord_length_of_power_bound v v (Nat.lt_two_pow_self).le

theorem natWord_length_le_of_le {v B : ℕ} (h : v ≤ 2 ^ B) : (natWord v).length ≤ 2 * B + 3 :=
  Cells.ParameterArithmetic.natWord_length_of_power_bound v B h

theorem intWord_length_le (z : ℤ) {B : ℕ} (h : z.natAbs ≤ 2 ^ B) :
    (NearCubicGates.Close.Interfaces.intWord z).length ≤ 2 * B + 8 := by
  unfold NearCubicGates.Close.Interfaces.intWord
  rw [List.length_append]
  have h1 : (natWord (if z < 0 then 1 else 0)).length ≤ 2 * 1 + 3 :=
    natWord_length_le_of_le (B := 1) (by split <;> norm_num)
  have h2 := natWord_length_le_of_le h
  omega

theorem flatMap_length_le' {α : Type} (f : α → List Bool) (B : ℕ) :
    ∀ xs : List α, (∀ x ∈ xs, (f x).length ≤ B) → (xs.flatMap f).length ≤ xs.length * B
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (by simp)
    have h2 := flatMap_length_le' f B l (fun x hx => h x (by simp [hx]))
    nlinarith

theorem listWord_length_le {α : Type} (f : α → List Bool) (xs : List α) (B : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ B) :
    (NearCubicGates.Close.Interfaces.listWord f xs).length ≤ 2 * xs.length + 3 + xs.length * B := by
  unfold NearCubicGates.Close.Interfaces.listWord
  rw [List.length_append]
  have h1 := natWord_length_le_self xs.length
  have h2 := flatMap_length_le' f B xs h
  omega

/-! ## The parameters of a child are below the preparation envelope -/

section Envelope

variable (q : ChildRequest B1 B2)

/-- The preparation envelope `V = preparationEnvelope B₁ n` of the call of a child. -/
noncomputable def envelope : ℕ := Cells.ParameterArithmetic.preparationEnvelope B1 q.call.n

theorem scalarBounds : Cells.ScalarPreparationBounds B1 (Builder.callInput q.call) q.selected.1 :=
  Cells.ParameterRules.scalar_preparation_bounds (rules q) B1
    (dispatch_admitted q.dispatched).1.2.2.2.2.2.2.2.2.2.1

theorem n_succ_le_envelope : q.call.n + 1 ≤ envelope q := Cells.ParameterArithmetic.preparation_envelope_arity B1 q.call.n

theorem P_le_envelope : q.selected.1.P ≤ envelope q := (scalarBounds q).P

theorem hE_le_envelope : q.selected.1.hE ≤ envelope q := (scalarBounds q).hE

theorem e_le_envelope : q.cellCall.e ≤ envelope q := (scalarBounds q).e

theorem J_le_envelope : q.cellCall.J + 1 ≤ envelope q + 1 := by
  have h := (scalarBounds q).J
  show q.selected.1.J - 1 + 1 ≤
    Cells.ParameterArithmetic.preparationEnvelope B1 (Builder.callInput q.call).n + 1
  omega

theorem G_le_envelope (j : Fin 2) : q.cellCall.G j ≤ envelope q := by
  have h1 := (scalarBounds q).omega1
  have h2 := (scalarBounds q).omega2
  have e1 := (rules q).omega1_eq
  have e2 := (rules q).omega2_eq
  have hm := (rules q).m_eq
  rw [hm] at e1 e2
  fin_cases j
  · show (Builder.callInput q.call).G1 ≤
      Cells.ParameterArithmetic.preparationEnvelope B1 (Builder.callInput q.call).n
    omega
  · show (Builder.callInput q.call).G2 ≤
      Cells.ParameterArithmetic.preparationEnvelope B1 (Builder.callInput q.call).n
    omega

end Envelope

/-! ## The index words of the printed tables -/

/-- An exponent for the index words and the systems: `(n+1)^{e₀}` dominates the polynomial `c V^5` of the sizes
below. -/
theorem pow_absorb (c n d : ℕ) (hn : 1 ≤ n) : c * (n + 1) ^ d ≤ (n + 1) ^ (d + c) := by
  rw [pow_add, mul_comm]
  apply Nat.mul_le_mul_left
  calc c ≤ 2 ^ c := (Nat.lt_two_pow_self).le
    _ ≤ (n + 1) ^ c := Nat.pow_le_pow_left (by omega) c

/-- The envelope is `C (n+1)^{B₁+12}`. -/
theorem envelope_eq (q : ChildRequest B1 B2) :
    envelope q = Cells.ParameterArithmetic.preparationCoefficient B1 * (q.call.n + 1) ^ (B1 + 12) := rfl

/-- **The index word of every printed table has polynomial size** (`prop:time`): for a part, a
pattern, a prime `p ∈ 𝒫`, a digit vector `δ ∈ digitSet` and a residue vector `ρ_Y` modulo `p`, the index word has
length at most `100 V^2`. -/
theorem printIndexWord_length_le_envelope (r : PrintRequest B1 B2) (hp : r.prime ∈ r.child.cellCall.primes)
    (hδ : r.digits ∈ digitSet r.child) (hρ : r.residues ∈ residueSet r.child r.prime) :
    (printIndexWord r).length ≤ 100 * envelope r.child ^ 2 := by
  classical
  set V := envelope r.child with hV
  have hV1 : r.child.call.n + 1 ≤ V := n_succ_le_envelope r.child
  have hpP : r.prime ≤ V := (le_P_of_mem_primes r.child hp).trans (P_le_envelope r.child)
  have hE : r.child.selected.1.hE ≤ V := hE_le_envelope r.child
  have hJ := J_le_envelope r.child
  -- the five fields
  have hs : (bitWord r.sign).length ≤ 5 := natWord_length_le_of_le (B := 1) (by split <;> norm_num)
  have hσ : (listWord bitWord (List.ofFn r.pattern)).length ≤ 2 * 8 + 3 + 8 * 5 := by
    have := listWord_length_le bitWord (List.ofFn r.pattern) 5
      (fun b _ => natWord_length_le_of_le (B := 1) (by split <;> norm_num))
    simpa using this
  have hpw : (natWord r.prime).length ≤ 2 * V + 3 := (natWord_length_le_self _).trans (by omega)
  have hdig : ∀ i j, (r.digits i j).natAbs ≤ 2 ^ V := by
    intro i j
    unfold digitSet at hδ
    rw [Fintype.mem_piFinset] at hδ
    have h := hδ i
    have hb : (r.digits i j).natAbs ≤ r.child.selected.1.hE := by
      split at h
      · rw [Fintype.mem_piFinset] at h
        have := Finset.mem_Ioo.mp (h j)
        omega
      · rw [Finset.mem_singleton] at h
        rw [h]
        simp
    exact hb.trans (hE.trans (Nat.lt_two_pow_self).le)
  have hδw : (listWord NearCubicGates.Close.Interfaces.intWord
      (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin (r.child.cellCall.J + 1) => r.digits i j).flatten).length ≤
      2 * (2 * (V + 1)) + 3 + 2 * (V + 1) * (2 * V + 8) := by
    have hlen : (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin (r.child.cellCall.J + 1) =>
        r.digits i j).flatten.length = 2 * (r.child.cellCall.J + 1) := by
      simp
      ring
    have h := listWord_length_le NearCubicGates.Close.Interfaces.intWord
      (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin (r.child.cellCall.J + 1) => r.digits i j).flatten
      (2 * V + 8) (fun x hx => by
        simp only [List.mem_flatten, List.mem_ofFn] at hx
        obtain ⟨l, ⟨i, rfl⟩, hxl⟩ := hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hxl
        exact intWord_length_le _ (hdig i j))
    rw [hlen] at h
    calc _ ≤ 2 * (2 * (r.child.cellCall.J + 1)) + 3 + 2 * (r.child.cellCall.J + 1) * (2 * V + 8) := h
      _ ≤ _ := by gcongr
  have hρw : (listWord NearCubicGates.Close.Interfaces.intWord (List.ofFn r.residues)).length ≤
      2 * 2 + 3 + 2 * (2 * V + 8) := by
    have h := listWord_length_le NearCubicGates.Close.Interfaces.intWord (List.ofFn r.residues) (2 * V + 8)
      (fun x hx => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
        apply intWord_length_le
        unfold residueSet at hρ
        rw [Fintype.mem_piFinset] at hρ
        have h := hρ j
        have hb : (r.residues j).natAbs ≤ r.prime := by
          split at h
          · have := Finset.mem_Ico.mp h
            omega
          · rw [Finset.mem_singleton] at h
            rw [h]
            simp
        exact hb.trans (hpP.trans (Nat.lt_two_pow_self).le))
    simpa using h
  unfold printIndexWord
  simp only [List.length_append]
  have hV5 : 5 ≤ V := by
    have := (dispatch_admitted r.child.dispatched).1.1
    omega
  nlinarith

/-- **The exponent of the index words**: on every child, every printed table has an index word of length at most
`(n+1)^{e₀}`. -/
theorem printIndexWord_length_le (B1 B2 : ℕ) :
    ∃ e₀ : ℕ, ∀ r : PrintRequest B1 B2, r.prime ∈ r.child.cellCall.primes → r.digits ∈ digitSet r.child →
      r.residues ∈ residueSet r.child r.prime → (printIndexWord r).length ≤ (r.child.call.n + 1) ^ e₀ := by
  refine ⟨2 * (B1 + 12) + 100 * Cells.ParameterArithmetic.preparationCoefficient B1 ^ 2, fun r hp hδ hρ => ?_⟩
  refine (printIndexWord_length_le_envelope r hp hδ hρ).trans ?_
  rw [envelope_eq, mul_pow, ← pow_mul, ← mul_assoc, mul_comm (B1 + 12) 2]
  exact pow_absorb _ _ _ (by have := (dispatch_admitted r.child.dispatched).1.1; omega)

/-! ## The exact systems -/

/-- The centred residue modulo `Q > 0` has absolute value at most `Q`. -/
theorem centeredResidue_natAbs_le (Q v : ℤ) (hQ : 0 < Q) : (Walks.centeredResidue Q v).natAbs ≤ Q.toNat := by
  unfold Walks.centeredResidue
  have h1 := Int.emod_nonneg (v + (Q - 1) / 2) hQ.ne'
  have h2 := Int.emod_lt_of_pos (v + (Q - 1) / 2) hQ
  have h3 : 0 ≤ (Q - 1) / 2 := Int.ediv_nonneg (by omega) (by norm_num)
  have h4 : (Q - 1) / 2 ≤ Q := by omega
  omega

/-- The coordinates of a box lie in `[-2mG_j, 2mG_j]`, and each coordinate list has at most `4mG_j + 1` entries. -/
theorem boxAxis_bounds (C : Algorithm.CellCall) (z : Fin C.ncol) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (j : Fin 2) :
    (boxAxis C z δ j).length ≤ 16 * C.G j + 1 ∧ ∀ x ∈ boxAxis C z δ j, x.natAbs ≤ 8 * C.G j := by
  unfold boxAxis
  split
  · refine ⟨?_, fun x hx => ?_⟩
    · rw [intervalList_length]
      have : ((2 * Algorithm.traceOrder : ℕ) : ℤ) = 8 := rfl
      rw [this]
      omega
    · rw [mem_intervalList] at hx
      have : ((2 * Algorithm.traceOrder : ℕ) : ℤ) = 8 := rfl
      rw [this] at hx
      omega
  · refine ⟨by simp, fun x hx => ?_⟩
    rw [List.mem_singleton] at hx
    simp [hx]

/-- **Every listed system has polynomial size** (`prop:time`): at most `10^5 V^5`. -/
theorem sysWord_length_le_envelope (q : ChildRequest B1 B2) (π : List Bool) (s : Bool) (z : Fin q.cellCall.ncol)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) :
    (Formats.sysWord (systemOf q.cellCall π s z σ δ)).length ≤ 100000 * envelope q ^ 5 := by
  classical
  set V := envelope q with hV
  have hV1 : q.call.n + 1 ≤ V := n_succ_le_envelope q
  have hn4 : 4 ≤ q.call.n := (dispatch_admitted q.dispatched).1.1
  have hV5 : 5 ≤ V := by omega
  have hP : q.selected.1.P ≤ V := P_le_envelope q
  have he : q.cellCall.e ≤ V := e_le_envelope q
  -- the points
  have hax : ∀ j, (boxAxis q.cellCall z δ j).length ≤ 17 * V ∧
      ∀ x ∈ boxAxis q.cellCall z δ j, x.natAbs ≤ 2 ^ (8 * V) := by
    intro j
    obtain ⟨h1, h2⟩ := boxAxis_bounds q.cellCall z δ j
    have hG := G_le_envelope q j
    refine ⟨by omega, fun x hx => (h2 x hx).trans ?_⟩
    exact (show 8 * q.cellCall.G j ≤ 8 * V by omega).trans (Nat.lt_two_pow_self).le
  have hpts_len : (boxPoints q.cellCall z δ).length ≤ 17 * V * (17 * V) := by
    unfold boxPoints
    rw [List.length_map, List.length_product]
    exact Nat.mul_le_mul (hax 0).1 (hax 1).1
  have hpt : ∀ u ∈ boxPoints q.cellCall z δ,
      (listWord NearCubicGates.Close.Interfaces.intWord u).length ≤ 2 * 2 + 3 + 2 * (2 * (8 * V) + 8) := by
    intro u hu
    unfold boxPoints at hu
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hu
    rw [List.mem_product] at hab
    have := listWord_length_le NearCubicGates.Close.Interfaces.intWord (pairList (a, b)) (2 * (8 * V) + 8)
      (fun x hx => by
        simp only [pairList, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact intWord_length_le _ ((hax 0).2 _ hab.1)
        · exact intWord_length_le _ ((hax 1).2 _ hab.2))
    simpa [pairList] using this
  have hptsw := listWord_length_le (listWord NearCubicGates.Close.Interfaces.intWord) (boxPoints q.cellCall z δ)
    _ hpt
  -- the rows
  have hrows_len : (systemOf q.cellCall π s z σ δ).rows.length ≤ V ^ 3 :=
    (systemRows_length_le q π s z σ δ).trans (Nat.pow_le_pow_left hP 3)
  have hrow : ∀ row ∈ (systemOf q.cellCall π s z σ δ).rows,
      (natWord row.1 ++ listWord natWord row.2.1 ++ natWord row.2.2).length ≤
        (2 * V + 3) + (2 * 2 + 3 + 2 * (2 * V + 3)) + (2 * (V * V) + 3) := by
    intro row hrow
    obtain ⟨p, hp, ρ, hρ, rfl⟩ := (mem_systemRows q.cellCall _ z σ δ row).mp hrow
    have hpV : p ≤ V := (le_P_of_mem_primes q hp).trans hP
    have hp1 : 1 ≤ p := one_le_of_mem_primes q hp
    have hρb : ∀ j, (ρ j).toNat ≤ V := by
      intro j
      rw [residueVectors_eq] at hρ
      unfold residueSet at hρ
      rw [Fintype.mem_piFinset] at hρ
      have h := hρ j
      split at h
      · have := Finset.mem_Ico.mp h
        omega
      · rw [Finset.mem_singleton] at h
        rw [h]
        simp
    simp only [systemRow, List.length_append]
    have hA : (natWord p).length ≤ 2 * V + 3 := (natWord_length_le_self p).trans (by omega)
    have hB : (listWord natWord [(ρ 0).toNat, (ρ 1).toNat]).length ≤ 2 * 2 + 3 + 2 * (2 * V + 3) := by
      have := listWord_length_le natWord [(ρ 0).toNat, (ρ 1).toNat] (2 * V + 3) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact (natWord_length_le_self _).trans (by have := hρb 0; omega)
        · exact (natWord_length_le_self _).trans (by have := hρb 1; omega))
      simpa using this
    have hC : (natWord (recoveredCountOf q.cellCall (splitWeight q.cellCall π s) z σ p δ ρ).toNat).length ≤
        2 * (V * V) + 3 := by
      apply natWord_length_le_of_le
      have hQ : (0 : ℤ) < (p : ℤ) ^ q.cellCall.e := by positivity
      have h1 := centeredResidue_natAbs_le ((p : ℤ) ^ q.cellCall.e)
        (printedCountOf q.cellCall (splitWeight q.cellCall π s) z σ p δ ρ) hQ
      have h2 : ((p : ℤ) ^ q.cellCall.e).toNat = p ^ q.cellCall.e := by
        rw [← Int.natCast_pow, Int.toNat_natCast]
      have h3 : p ^ q.cellCall.e ≤ 2 ^ (V * V) :=
        calc p ^ q.cellCall.e ≤ (2 ^ V) ^ q.cellCall.e :=
              Nat.pow_le_pow_left (hpV.trans (Nat.lt_two_pow_self).le) _
          _ = 2 ^ (V * q.cellCall.e) := by rw [← pow_mul]
          _ ≤ 2 ^ (V * V) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ he)
      unfold recoveredCountOf
      calc (Walks.centeredResidue ((p : ℤ) ^ q.cellCall.e)
            (printedCountOf q.cellCall (splitWeight q.cellCall π s) z σ p δ ρ)).toNat
          ≤ (Walks.centeredResidue ((p : ℤ) ^ q.cellCall.e)
            (printedCountOf q.cellCall (splitWeight q.cellCall π s) z σ p δ ρ)).natAbs := by omega
        _ ≤ 2 ^ (V * V) := by rw [h2] at h1; exact h1.trans h3
    omega
  have hrowsw := listWord_length_le (fun row : ℕ × List ℕ × ℕ =>
    natWord row.1 ++ listWord natWord row.2.1 ++ natWord row.2.2) _ _ hrow
  unfold Formats.sysWord
  rw [List.length_append]
  change (listWord (listWord NearCubicGates.Close.Interfaces.intWord) (boxPoints q.cellCall z δ)).length +
    (listWord (fun row : ℕ × List ℕ × ℕ => natWord row.1 ++ listWord natWord row.2.1 ++ natWord row.2.2)
      (systemOf q.cellCall π s z σ δ).rows).length ≤ _
  have hV2 : V ^ 2 ≤ V ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hV3 : V ^ 3 ≤ V ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hV4 : V ^ 4 ≤ V ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hV1' : V ≤ V ^ 5 := Nat.le_self_pow (by norm_num) V
  have hone : 1 ≤ V ^ 5 := Nat.one_le_pow _ _ (by omega)
  -- the two parts
  have hP1 : (listWord (listWord NearCubicGates.Close.Interfaces.intWord) (boxPoints q.cellCall z δ)).length ≤
      30000 * V ^ 5 := by
    refine hptsw.trans ?_
    have hm := Nat.mul_le_mul_right (2 * 2 + 3 + 2 * (2 * (8 * V) + 8)) hpts_len
    nlinarith
  have hP2 : (listWord (fun row : ℕ × List ℕ × ℕ => natWord row.1 ++ listWord natWord row.2.1 ++ natWord row.2.2)
      (systemOf q.cellCall π s z σ δ).rows).length ≤ 70000 * V ^ 5 := by
    refine hrowsw.trans ?_
    have hm := Nat.mul_le_mul_right ((2 * V + 3) + (2 * 2 + 3 + 2 * (2 * V + 3)) + (2 * (V * V) + 3)) hrows_len
    nlinarith
  omega

/-- **The exponent of the systems**: on every child, every listed system has a word of length at most
`(n+1)^{e₀}`. -/
theorem sysWord_length_le (B1 B2 : ℕ) :
    ∃ e₀ : ℕ, ∀ (q : ChildRequest B1 B2) (π : List Bool) (s : Bool) (z : Fin q.cellCall.ncol)
      (σ : Cycle.SignPattern Algorithm.traceOrder) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ),
      (Formats.sysWord (systemOf q.cellCall π s z σ δ)).length ≤ (q.call.n + 1) ^ e₀ := by
  refine ⟨5 * (B1 + 12) + 100000 * Cells.ParameterArithmetic.preparationCoefficient B1 ^ 5,
    fun q π s z σ δ => ?_⟩
  refine (sysWord_length_le_envelope q π s z σ δ).trans ?_
  rw [envelope_eq, mul_pow, ← pow_mul, ← mul_assoc, mul_comm (B1 + 12) 5]
  exact pow_absorb _ _ _ (by have := (dispatch_admitted q.dispatched).1.1; omega)

end NearQuarticWires.Reconstruct
