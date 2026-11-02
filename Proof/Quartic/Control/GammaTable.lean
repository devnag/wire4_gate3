import Proof.Quartic.Control.GammaCost

/-!
# The control of the coefficient stage

Paper: Step 3 of `sec:algorithm`, paper/paper.tex; `cor:conditional`; `prop:time`: for each of the `N^{2m}` closed walks, one coefficient evaluation and a polynomial overhead; the child
input is read once.

`gammaTableControl` packages the program `gammaP` of the coefficient program by `Expand.PolyTab.wordFunction_of_ideal`
(imported from `Proof.Gates.Expand.PolyTabPack`) into the field `Greedy.GammaTableControl`. Its run is
`gammaRun_exec`; its cost is `gammaRunCost_le` together with `gammaY_le`: the size `Y` is polynomial in `n` on a
dispatched call.
-/

set_option autoImplicit false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces (Call callWord listWord)
open NearQuarticWires.Program NearQuarticWires.Greedy

/-- The constant of the size bound. -/
def gammaCY (B1 : ℕ) : ℕ :=
  2 ^ 11 + 100 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 4) * 2 ^ (12 * (B1 + 12)) + 8 * (2 * B1 + 103) + 10

/-- The degree of the size bound. -/
def gammaD (B1 B2 : ℕ) : ℕ := (B2 + 9) * (B1 + 12) + 1

variable {B1 B2 : ℕ}

theorem pow_le_pow_of_le' (n a D : ℕ) (h : a ≤ D) : (n + 1) ^ a ≤ (n + 1) ^ D :=
  Nat.pow_le_pow_right (by omega) h

/-- **The size is polynomial in `n`.** -/
theorem gammaY_le (q : ChildRequest B1 B2) : gammaY q ≤ gammaCY B1 * (q.call.n + 1) ^ gammaD B1 B2 := by
  have hd := q.dispatched
  have hL : (callWord q.call).length ≤ 2 ^ 11 * (q.call.n + 1) ^ (B2 + 9) :=
    (callWord_length_le (dispatch_admitted hd).1).trans (callBound_le B2 q.call.n)
  have hP := Cells.dispatched_parametersWord_length hd
  have hS : q.selected.1.S ≤ 8 * (2 * B1 + 103) * (q.call.n + 1) := by
    have := seedRounds_le (B1 := B1) (B2 := B2) q.call
    rwa [seedRounds_of_dispatch hd q.witness, seedLength_runCall] at this
  set m := q.call.n + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hL1 : (callWord q.call).length + 1 ≤ 2 ^ 12 * m ^ (B2 + 9) := by
    have : 1 ≤ m ^ (B2 + 9) := Nat.one_le_pow _ _ hm1
    rw [show 2 ^ 12 = 2 * 2 ^ 11 by norm_num]; nlinarith
  have hLp : ((callWord q.call).length + 1) ^ (B1 + 12) ≤ 2 ^ (12 * (B1 + 12)) * m ^ ((B2 + 9) * (B1 + 12)) := by
    calc ((callWord q.call).length + 1) ^ (B1 + 12) ≤ (2 ^ 12 * m ^ (B2 + 9)) ^ (B1 + 12) := Nat.pow_le_pow_left hL1 _
      _ = 2 ^ (12 * (B1 + 12)) * m ^ ((B2 + 9) * (B1 + 12)) := by rw [mul_pow, ← pow_mul, ← pow_mul]
  have h1 : m ^ (B2 + 9) ≤ m ^ gammaD B1 B2 := pow_le_pow_of_le' _ _ _ (by unfold gammaD; nlinarith)
  have h2 : m ^ ((B2 + 9) * (B1 + 12)) ≤ m ^ gammaD B1 B2 := pow_le_pow_of_le' _ _ _ (by unfold gammaD; omega)
  have h3 : m ≤ m ^ gammaD B1 B2 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ gammaD B1 B2 := pow_le_pow_of_le' _ _ _ (by unfold gammaD; omega)
  have h4 : 1 ≤ m ^ gammaD B1 B2 := Nat.one_le_pow _ _ hm1
  set M := m ^ gammaD B1 B2 with hM
  have e1 : (callWord q.call).length ≤ 2 ^ 11 * M := le_trans hL (Nat.mul_le_mul_left _ h1)
  have e2 : (parametersWord q.selected.1).length ≤ 100 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 4) * 2 ^ (12 * (B1 + 12)) * M := by
    calc _ ≤ 100 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 4) * ((callWord q.call).length + 1) ^ (B1 + 12) := hP
      _ ≤ 100 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 4) * (2 ^ (12 * (B1 + 12)) * m ^ ((B2 + 9) * (B1 + 12))) :=
        Nat.mul_le_mul_left _ hLp
      _ ≤ 100 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 4) * (2 ^ (12 * (B1 + 12)) * M) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
      _ = _ := by ring
  have e3 : q.selected.1.S ≤ 8 * (2 * B1 + 103) * M := le_trans hS (Nat.mul_le_mul_left _ h3)
  unfold gammaY gammaCY
  nlinarith [e1, e2, e3, h4]


/-- The exponent of the polynomial overhead per walk. -/
def gammaE (B1 B2 : ℕ) : ℕ := 2 * gammaD B1 B2

/-- The constant of the cost. -/
def gammaK (B1 : ℕ) : ℕ := 200000 * gammaCY B1 ^ 2 + 2

theorem gammaCY_pos (B1 : ℕ) : 1 ≤ gammaCY B1 := by unfold gammaCY; omega

/-- **The cost fits the budget of `Greedy.GammaTableControl`.** -/
theorem gammaBudget_le (q : ChildRequest B1 B2) (B : ℕ)
    (hγ : ∀ x ∈ gammaTable q, (NearCubicGates.Close.Interfaces.intWord x).length ≤ B + 1) :
    2 * gammaRunCost q B + 2 ≤ gammaK B1 * ((q.cellCall.seed.N ^ (2 * Algorithm.traceOrder) + 1) *
      (B + (q.call.n + 1) ^ gammaE B1 B2 + q.seedPrefix.length) + (childInput q).length + 1) := by
  have hc := gammaRunCost_le q B hγ
  have hN : q.cellCall.seed.N ^ (2 * Algorithm.traceOrder) = 2 ^ (q.selected.1.k / 2 * 8) := by
    show (2 ^ q.cellCall.seed.kh) ^ (2 * 4) = _
    rw [← pow_mul, seed_kh]
  rw [hN]
  have hY := gammaY_le q
  have hC1 := gammaCY_pos B1
  set N8 := 2 ^ (q.selected.1.k / 2 * 8) with hN8
  set X := (q.call.n + 1) ^ gammaE B1 B2 with hX
  set C := gammaCY B1 with hC
  have hY2 : gammaY q ^ 2 ≤ C ^ 2 * X := by
    have h := Nat.pow_le_pow_left hY 2
    rw [mul_pow, ← pow_mul] at h
    rw [hX, gammaE, Nat.mul_comm 2 (gammaD B1 B2)]
    exact h
  have hC2 : 1 ≤ C ^ 2 := Nat.one_le_pow _ _ hC1
  have h1 : B + gammaY q ^ 2 ≤ C ^ 2 * (B + X + q.seedPrefix.length) := by nlinarith
  have h2 : (N8 + 1) * (B + gammaY q ^ 2) ≤ C ^ 2 * ((N8 + 1) * (B + X + q.seedPrefix.length)) := by
    calc (N8 + 1) * (B + gammaY q ^ 2) ≤ (N8 + 1) * (C ^ 2 * (B + X + q.seedPrefix.length)) :=
          Nat.mul_le_mul_left _ h1
      _ = C ^ 2 * ((N8 + 1) * (B + X + q.seedPrefix.length)) := by ring
  set A := (N8 + 1) * (B + X + q.seedPrefix.length) with hA
  have hA1 : 0 ≤ A := Nat.zero_le _
  unfold gammaK
  rw [← hC]
  nlinarith

/-- **The control of the coefficient stage** (`Greedy.GammaTableControl`, Step 3 of `sec:algorithm`, paper/paper.tex, with `cor:conditional`, and `prop:time`): for every word function
computing one coefficient, the program `gammaP` of that word function, packaged by
`Expand.PolyTab.wordFunction_of_ideal`, maps the child input to the framed `gammaWord` within
`K ((N^{2m} + 1)(gammaBound + (n+1)^e + |π|) + |childInput| + 1)` steps. -/
noncomputable def gammaTableControl (B1 B2 : ℕ) : GammaTableControl B1 B2 where
  K := gammaK B1
  e := gammaE B1 B2
  program := fun gammaBudget gammaBound f hb =>
    NearCubicGates.Close.Expand.PolyTab.wordFunction_of_ideal (gammaP f.program) (cOUT _) (by simp [cOUT])
      (fun q => gammaCap q (gammaBound q.call q.witness)) (fun _ _ => 0)
      (fun q => gammaRunCost q (gammaBound q.call q.witness))
      (fun q => gammaBudget_le q _ (fun x hx => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
        have := output_length_le f (gammaRequest q w)
        rw [gammaTarget_gammaRequest] at this
        have := hb q w
        omega))
      (fun q => ⟨rfl, gammaRun_exec f q _ (hb q)⟩)

end NearQuarticWires.Control
