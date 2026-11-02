import Proof.Quartic.Reconstruct.PrintPack

/-!
# The cost of the printing stage

Paper: `prop:time`, paper/paper.tex.

The loop nest writes at most `512 P^{2J+5} = tableCount q` tables, each within `reqCost` steps (`sigCost_le`,
`nest_le`); one request costs at most `7000 U^2 (|prepWord| + |u| + 1)` steps (`reqCost_le`); the input and the
context cost at most `4000 U^3 + 101 |γ|` steps (`pre_le`). Together `printRunCost_le`: the run costs at most
`20000 U^3 · printsCost q` steps, with `U = a₁ 4^{c₁} (n+1)^{c₁}` (`scalePU`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord callWord)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- **The cost of the loop nest.** -/
theorem sigCost_le (rp : RP) (np : NP) (N : ℕ) (hN : 1 ≤ N) (hL : np.ps.length ≤ N) (hPm : np.Pm ≤ N)
    (h0 : 1 ≤ np.A0) (h1 : 1 ≤ np.A1) :
    2 * sigCost rp np ≤ 512 * (np.A0 * np.A1 * N ^ 3) * (reqCost rp.ℓ rp.J1 rp.pw.length rp.u.length + 64) := by
  set R := reqCost rp.ℓ rp.J1 rp.pw.length rp.u.length
  set L := np.ps.length
  set Pm := np.Pm
  set A0 := np.A0
  set A1 := np.A1
  have hres : resCost rp Pm ≤ N ^ 2 * (R + 16) := by
    unfold resCost
    have a1 : Pm * (R + 4) ≤ N * (R + 4) := Nat.mul_le_mul_right _ hPm
    have a2 : Pm * (Pm * (R + 4) + 4 + 4) ≤ N * (N * (R + 4) + 4 + 4) := Nat.mul_le_mul hPm (by omega)
    have a3 : N * (N * (R + 4) + 4 + 4) + 4 ≤ N ^ 2 * (R + 16) := by nlinarith
    exact (Nat.add_le_add_right a2 4).trans a3
  have hprime : primeCost rp np ≤ N ^ 3 * (R + 43) := by
    unfold primeCost
    have b1 : L + 1 + (L * 5 + 4) + 3 + 3 + resCost rp Pm + 2 + 4 ≤ 6 * N + 17 + N ^ 2 * (R + 16) := by omega
    have b2 := Nat.mul_le_mul hL b1
    have b3 : N * (6 * N + 17 + N ^ 2 * (R + 16)) + 4 ≤ N ^ 3 * (R + 43) := by
      have e : N ^ 3 * (R + 43) = N * (N ^ 2 * (R + 16)) + 27 * N ^ 3 := by ring
      have f1 : N ≤ N ^ 2 := by nlinarith
      have f2 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right hN (by norm_num)
      have e2 : N * (6 * N + 17 + N ^ 2 * (R + 16)) = 6 * N ^ 2 + 17 * N + N * (N ^ 2 * (R + 16)) := by ring
      rw [e, e2]
      omega
    exact (Nat.add_le_add_right b2 4).trans b3
  have hd1 : d1Cost rp np ≤ A1 * (N ^ 3 * (R + 51)) := by
    unfold d1Cost
    have c1 : primeCost rp np + 4 ≤ N ^ 3 * (R + 51) - 4 := by
      have : 8 ≤ N ^ 3 * 8 := by have := Nat.one_le_pow 3 N hN; omega
      have e : N ^ 3 * (R + 51) = N ^ 3 * (R + 43) + N ^ 3 * 8 := by ring
      omega
    have c2 := Nat.mul_le_mul_left A1 c1
    have c3 : A1 * (N ^ 3 * (R + 51) - 4) + 4 ≤ A1 * (N ^ 3 * (R + 51)) := by
      have : 4 ≤ N ^ 3 * (R + 51) := by have := Nat.one_le_pow 3 N hN; nlinarith
      rw [Nat.mul_sub]
      have : A1 * 4 ≤ A1 * (N ^ 3 * (R + 51)) := Nat.mul_le_mul_left _ this
      omega
    exact (Nat.add_le_add_right c2 4).trans c3
  have hd0 : d0Cost rp np ≤ A0 * (A1 * (N ^ 3 * (R + 59))) := by
    unfold d0Cost
    have g1 : 8 ≤ A1 * (N ^ 3 * 8) := by
      have := Nat.one_le_pow 3 N hN
      have : 8 ≤ N ^ 3 * 8 := by omega
      exact this.trans (Nat.le_mul_of_pos_left _ h1)
    have e : A1 * (N ^ 3 * (R + 59)) = A1 * (N ^ 3 * (R + 51)) + A1 * (N ^ 3 * 8) := by ring
    have c1 : d1Cost rp np + 4 ≤ A1 * (N ^ 3 * (R + 59)) - 4 := by omega
    have c2 := Nat.mul_le_mul_left A0 c1
    have c3 : A0 * (A1 * (N ^ 3 * (R + 59)) - 4) + 4 ≤ A0 * (A1 * (N ^ 3 * (R + 59))) := by
      have h4 : 4 ≤ A1 * (N ^ 3 * (R + 59)) := by omega
      rw [Nat.mul_sub]
      have : A0 * 4 ≤ A0 * (A1 * (N ^ 3 * (R + 59))) := Nat.mul_le_mul_left _ h4
      omega
    exact (Nat.add_le_add_right c2 4).trans c3
  unfold sigCost
  have g : 5 ≤ A0 * (A1 * (N ^ 3 * 5)) := by
    have := Nat.one_le_pow 3 N hN
    have h5 : 5 ≤ N ^ 3 * 5 := by omega
    have : 5 ≤ A1 * (N ^ 3 * 5) := h5.trans (Nat.le_mul_of_pos_left _ h1)
    exact this.trans (Nat.le_mul_of_pos_left _ h0)
  have e : 512 * (A0 * A1 * N ^ 3) * (R + 64) =
      512 * (A0 * (A1 * (N ^ 3 * (R + 59)))) + 512 * (A0 * (A1 * (N ^ 3 * 5))) := by ring
  rw [e]
  omega

theorem emitNatDCost_two (x : ℕ) : emitNatDCost 2 x = 36 * x + 108 := by unfold emitNatDCost; norm_num; ring

theorem emitNatDCost_one (x : ℕ) : emitNatDCost 1 x = 28 * x + 84 := by unfold emitNatDCost; norm_num; ring

/-- **The cost of one request.** -/
theorem reqCost_le (ℓ J1 PL Uu U : ℕ) (hU : 1 ≤ U) (hℓ : ℓ ≤ U) (hJ : J1 ≤ U) :
    reqCost ℓ J1 PL Uu + 64 ≤ 7000 * U ^ 2 * (PL + Uu + 1) := by
  have hp : printIdxCost ℓ J1 = 144 * (J1 * ℓ) + 480 * J1 + 324 * ℓ + 2302 := by
    unfold printIdxCost emitShiftCost; rw [emitNatDCost_two, emitNatDCost_two]; ring
  have hr : reqCost ℓ J1 PL Uu = 2 * printIdxCost ℓ J1 + 17 * PL + 30 * Uu + 61 := by unfold reqCost; ring
  have hJl : J1 * ℓ ≤ U ^ 2 := by rw [sq]; exact Nat.mul_le_mul hJ hℓ
  have hU2 : U ≤ U ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hP : PL ≤ U ^ 2 * PL := Nat.le_mul_of_pos_left _ (by positivity)
  have hQ : Uu ≤ U ^ 2 * Uu := Nat.le_mul_of_pos_left _ (by positivity)
  have e : 7000 * U ^ 2 * (PL + Uu + 1) = 7000 * (U ^ 2 * PL) + 7000 * (U ^ 2 * Uu) + 7000 * U ^ 2 := by ring
  rw [hr, hp, e]
  omega

/-- The scale `U = a₁ 4^{c₁} (n+1)^{c₁}` of the printing stage of a child. -/
noncomputable def scalePU (B1 B2 : ℕ) (q : ChildRequest B1 B2) : ℕ :=
  printA B1 * 4 ^ prepE B1 B2 * (q.call.n + 1) ^ prepE B1 B2

theorem scalePU_facts (q : ChildRequest B1 B2) :
    printA B1 ≤ scalePU B1 B2 q ∧ prepE B1 B2 ≤ scalePU B1 B2 q ∧ q.call.n + 1 ≤ scalePU B1 B2 q ∧
      128 ≤ scalePU B1 B2 q ∧ printW B1 B2 q ≤ scalePU B1 B2 q := by
  set c1 := prepE B1 B2 with hc1
  have hc96 : 96 ≤ c1 := by rw [hc1]; unfold prepE; nlinarith
  have ha : 64 ≤ printA B1 := by unfold printA; omega
  have h4 : 2 ^ c1 ≤ 4 ^ c1 := Nat.pow_le_pow_left (by norm_num) _
  have h4' : 256 ≤ 4 ^ c1 := (show 256 = 4 ^ 4 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc : c1 < 2 ^ c1 := Nat.lt_two_pow_self
  have hP : q.call.n + 1 ≤ (q.call.n + 1) ^ c1 := by
    calc q.call.n + 1 = (q.call.n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hP1 : 1 ≤ (q.call.n + 1) ^ c1 := Nat.one_le_pow _ _ (by omega)
  have hA4 : printA B1 * 4 ^ c1 ≤ printA B1 * 4 ^ c1 * (q.call.n + 1) ^ c1 := Nat.le_mul_of_pos_right _ hP1
  have hA : printA B1 ≤ printA B1 * 4 ^ c1 := Nat.le_mul_of_pos_right _ (by omega)
  have h44 : 4 ^ c1 ≤ printA B1 * 4 ^ c1 := Nat.le_mul_of_pos_left _ (by omega)
  have hn : (q.call.n + 1) ^ c1 ≤ printA B1 * 4 ^ c1 * (q.call.n + 1) ^ c1 :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
  unfold scalePU
  rw [← hc1]
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  unfold printW Sz.W printSizes
  simp only
  rw [leadOnes_gammaWord, ← hc1]
  have h := NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le q.call.n
  calc 2 ^ (c1 * (1 + natBitLength q.call.n)) * printA B1 = printA B1 * 2 ^ c1 * (2 ^ natBitLength q.call.n) ^ c1 := by
        rw [mul_add, mul_one, pow_add, ← pow_mul, mul_comm (natBitLength q.call.n) c1]; ring
    _ ≤ printA B1 * 2 ^ c1 * (2 * (q.call.n + 1)) ^ c1 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
    _ = printA B1 * (2 ^ c1 * 2 ^ c1) * (q.call.n + 1) ^ c1 := by rw [mul_pow]; ring
    _ = printA B1 * 4 ^ c1 * (q.call.n + 1) ^ c1 := by rw [← mul_pow]; norm_num

end NearQuarticWires.Reconstruct
