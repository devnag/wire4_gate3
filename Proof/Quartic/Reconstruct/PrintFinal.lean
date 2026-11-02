import Proof.Quartic.Reconstruct.PrintBudget

/-!
# The printing stage within `K (n+1)^e` times its cost

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

`printRunCost_le`: the run costs at most `20000 U^3 · printsCost q` steps. `printBudget_le`: the compiled budget of the
printing stage is at most `printsK B₁ B₂ (n+1)^{printsE B₁ B₂} · printsCost q`. `printsStage` is the stage
`gammaWord ↦ frame printsWord` with this budget, the `prints` field of `ReconstructPhases`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord callWord)
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearCubicWires.RepairOrdinary (WordFunction frame)

variable {B1 B2 : ℕ}

theorem natBitLength_cntOf_le (q : ChildRequest B1 B2) :
    natBitLength (cntOf q) ≤ envelope q * (2 * envelope q + 5) + 10 := by
  obtain ⟨-, -, -, b4, -⟩ := cntOf_le q
  exact natBitLength_le_of_lt_two_pow (lt_of_le_of_lt b4 (bigOf_lt q)) (by omega)

/-- **The input, the context and the count cost at most `4000 U^3 + 101 |γ|` steps.** -/
theorem pre_le (q : ChildRequest B1 B2) (W U : ℕ) (hU : 128 ≤ U) (hWU : W ≤ U) (hpw : printWidth q ≤ W) :
    printPreCost q W + (q.cellCall.J * 7 + emitNatDCost 1 (natBitLength (cntOf q)) + 90) + 1 ≤
      4000 * U ^ 3 + 101 * (gammaWord q).length := by
  unfold printWidth at hpw
  set V := envelope q with hV
  obtain ⟨-, -, -, -, hn, hJ, -⟩ := child_le q
  have hPV := P_le_envelope q
  have hl := length_primes_le q
  have hV3 := env_cube V
  have hV1 : V + 1 ≤ (V + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hcb : natBitLength (cntOf q) ≤ V * (2 * V + 5) + 10 := natBitLength_cntOf_le q
  have hpl := congrArg List.length (prepWord_split q)
  simp only [List.length_cons, List.length_append, RepairOrdinary.frame_length] at hpl
  have hγl := congrArg List.length (gammaWord_split q)
  simp only [List.length_cons, List.length_append, RepairOrdinary.frame_length] at hγl
  rw [certifiedBits_length] at hγl
  have h1 : ((callWord q.call).length + 1) ^ 3 ≤ U ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h2 : ((parametersWord q.selected.1).length + 1) ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hU2 : 128 * U ≤ U ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hU
  have hU3 : 128 * U ^ 2 ≤ U ^ 3 := by rw [pow_succ]; rw [mul_comm]; exact Nat.mul_le_mul_left _ hU
  have hJW : q.cellCall.J * (36 * (W - 3) + 108 + 6) ≤ 36 * U ^ 2 + 114 * U := by
    calc q.cellCall.J * (36 * (W - 3) + 108 + 6) ≤ U * (36 * U + 114) := Nat.mul_le_mul (by omega) (by omega)
      _ = 36 * U ^ 2 + 114 * U := by ring
  unfold printPreCost printHeadCost scanCallCost scanParamsCost ctxCost
  rw [emitNatDCost_two, emitNatDCost_two, emitNatDCost_one]
  omega

theorem tableCount_eq (q : ChildRequest B1 B2) :
    tableCount q = 512 * q.selected.1.P ^ (2 * q.cellCall.J + 5) := by
  unfold tableCount
  rw [show 2 * (q.cellCall.J + 1) + 3 = 2 * q.cellCall.J + 5 by ring]
  norm_num

/-- **The run of the printing stage costs at most `20000 U^3 · printsCost q` steps.** -/
theorem printRunCost_le (q : ChildRequest B1 B2) :
    printRunCost q (printW B1 B2 q) + (gammaWord q).length + 1 ≤ 20000 * scalePU B1 B2 q ^ 3 * printsCost q := by
  obtain ⟨-, -, -, hU, hWU⟩ := scalePU_facts q
  set U := scalePU B1 B2 q
  set W := printW B1 B2 q
  have hpw : printWidth q ≤ W := printWidth_le q
  have hpre := pre_le q W U hU hWU hpw
  unfold printRunCost printPostCost
  unfold printWidth at hpw
  set V := envelope q with hV
  obtain ⟨-, -, -, -, hn, hJ, -⟩ := child_le q
  have hPV := P_le_envelope q
  have hP := one_le_P q
  have hV1 : V + 1 ≤ (V + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  set P := q.selected.1.P
  set J := q.cellCall.J
  -- the loop nest
  have hs : 2 * sigCost (rpOf q (W - 3)) (npOf q P) ≤ 512 * (baseOf q ^ (J + 1) * a1Of q * P ^ 3) *
      (reqCost (W - 3) (J + 1) (prepWord B1 B2 q.call q.witness).length
        (listWord NearCubicGates.Close.Interfaces.intWord (gammaTable q)).length + 64) :=
    sigCost_le (rpOf q (W - 3)) (npOf q P) P hP (length_primes_le q) le_rfl
      (Nat.one_le_pow _ _ (one_le_baseOf q)) (one_le_a1Of q)
  have hreq := reqCost_le (W - 3) (J + 1) (prepWord B1 B2 q.call q.witness).length
    (listWord NearCubicGates.Close.Interfaces.intWord (gammaTable q)).length U (by omega) (by omega) (by omega)
  have hX : baseOf q ^ (J + 1) * a1Of q * P ^ 3 ≤ P ^ (2 * J + 5) := by
    have hA0 : baseOf q ^ (J + 1) ≤ P ^ (J + 1) := Nat.pow_le_pow_left (baseOf_le q) _
    have hA1 : a1Of q ≤ P ^ (J + 1) := a1Of_le q
    have e : P ^ (2 * J + 5) = P ^ (J + 1) * P ^ (J + 1) * P ^ 3 := by rw [← pow_add, ← pow_add]; ring_nf
    rw [e]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hA0 hA1)
  have hu : (listWord NearCubicGates.Close.Interfaces.intWord (gammaTable q)).length + 1 ≤ (gammaTableWord q).length := by
    unfold gammaTableWord; rw [RepairOrdinary.frame_length]; omega
  have hZ : 1 ≤ (q.call.n + 1) ^ sizeExp B1 B2 := Nat.one_le_pow _ _ (by omega)
  set Y := (prepWord B1 B2 q.call q.witness).length + (gammaTableWord q).length + (q.call.n + 1) ^ sizeExp B1 B2
    with hY
  set T := tableCount q with hT
  have hTe : T = 512 * P ^ (2 * J + 5) := tableCount_eq q
  have hsig : 2 * sigCost (rpOf q (W - 3)) (npOf q P) ≤ 7000 * (U ^ 2 * (T * Y)) := by
    calc 2 * sigCost (rpOf q (W - 3)) (npOf q P) ≤ _ := hs
      _ ≤ T * (7000 * U ^ 2 * ((prepWord B1 B2 q.call q.witness).length +
            (listWord NearCubicGates.Close.Interfaces.intWord (gammaTable q)).length + 1)) :=
          Nat.mul_le_mul (by rw [hTe]; exact Nat.mul_le_mul_left 512 hX) hreq
      _ ≤ T * (7000 * U ^ 2 * Y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      _ = 7000 * (U ^ 2 * (T * Y)) := by ring
  have hT1 : 1 ≤ T := by rw [hTe]; have := Nat.one_le_pow (2 * J + 5) P hP; omega
  have hY1 : 1 ≤ Y := by omega
  have hM : 1 ≤ T * Y := Nat.mul_pos hT1 hY1
  have hU23 : U ^ 2 ≤ U ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hU3 : 1 ≤ U ^ 3 := Nat.one_le_pow _ _ (by omega)
  have m1 : U ^ 2 * (T * Y) ≤ U ^ 3 * (T * Y) := Nat.mul_le_mul_right _ hU23
  have m2 : (gammaWord q).length ≤ U ^ 3 * (gammaWord q).length := Nat.le_mul_of_pos_left _ hU3
  have m3 : U ^ 3 ≤ U ^ 3 * (T * Y) := Nat.le_mul_of_pos_right _ hM
  have hc : printsCost q = T * Y + (gammaWord q).length + 1 := rfl
  have e : 20000 * U ^ 3 * (T * Y + (gammaWord q).length + 1) =
      20000 * (U ^ 3 * (T * Y)) + 20000 * (U ^ 3 * (gammaWord q).length) + 20000 * U ^ 3 := by ring
  rw [hc, e]
  omega

/-- The constant of the printing stage. -/
noncomputable def printsK (B1 B2 : ℕ) : ℕ :=
  200000000 * (201 + emitTapes) ^ 2 * (printA B1 * 4 ^ prepE B1 B2) ^ 5

/-- The exponent of the printing stage. -/
def printsE (B1 B2 : ℕ) : ℕ := 5 * prepE B1 B2

theorem scalePU_pow (q : ChildRequest B1 B2) :
    scalePU B1 B2 q ^ 5 = (printA B1 * 4 ^ prepE B1 B2) ^ 5 * (q.call.n + 1) ^ printsE B1 B2 := by
  unfold scalePU printsE
  rw [mul_pow, ← pow_mul, mul_comm (prepE B1 B2) 5]

/-- **The budget of the printing stage.** -/
theorem printBudget_le (q : ChildRequest B1 B2) :
    printBudget B1 B2 q ≤ printsK B1 B2 * (q.call.n + 1) ^ printsE B1 B2 * printsCost q := by
  obtain ⟨ha, hc, hn, h128, hWU⟩ := scalePU_facts q
  have hN := printRunCost_le q
  set U := scalePU B1 B2 q with hU
  set T := emitTapes with hT
  set S := U + 200 + T with hS
  have hL : leadOnes (gammaWord q) ≤ S := by
    rw [leadOnes_gammaWord]; have := natBitLength_le_succ' q.call.n; omega
  have hlang := NearQuarticWires.StageMain.Runtime.langBudget_le
    NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (printSizes B1 B2) VV MM (gammaWord q)
    (printRunCost q (printW B1 B2 q)) S (by omega) (show (128 : ℕ) ≤ S by omega) (show (10 : ℕ) ≤ S by omega)
    (show T ≤ S by omega) (show printA B1 ≤ S by omega) (show prepE B1 B2 ≤ S by omega) (by simp [printSizes])
    (by simp [printSizes]) (by simp [printSizes]) (by simp [printSizes]) hL (show printW B1 B2 q ≤ S by omega)
    (by simp [Sz.Lk, printSizes]) (by simp [Sz.Bk, printSizes])
  have hSU : S ≤ (201 + T) * U := by nlinarith
  have hS2 : S ^ 2 ≤ (201 + T) ^ 2 * U ^ 2 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hSU 2
  calc printBudget B1 B2 q ≤ 10000 * S ^ 2 * (printRunCost q (printW B1 B2 q) + (gammaWord q).length + 1) := hlang
    _ ≤ 10000 * ((201 + T) ^ 2 * U ^ 2) * (20000 * U ^ 3 * printsCost q) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hS2) hN
    _ = 200000000 * (201 + T) ^ 2 * U ^ 5 * printsCost q := by ring
    _ = printsK B1 B2 * (q.call.n + 1) ^ printsE B1 B2 * printsCost q := by
        rw [scalePU_pow]; unfold printsK; ring

/-- **The printing stage** `gammaWord ↦ frame printsWord` within `printsK B₁ B₂ (n+1)^{printsE B₁ B₂} printsCost q`:
the `prints` field of `ReconstructPhases`. -/
noncomputable def printsStage (B1 B2 : ℕ) :
    WordFunction (ChildRequest B1 B2) gammaWord (fun q => frame (printsWord q))
      (fun q => printsK B1 B2 * (q.call.n + 1) ^ printsE B1 B2 * printsCost q) :=
  WordFunction.enlargeBudget (printWF B1 B2) printBudget_le

end NearQuarticWires.Reconstruct
