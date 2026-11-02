import Proof.Quartic.Control.GammaControl
import Proof.Quartic.Cells.ParametersCallEncoding

/-!
# The cost of the coefficient stage

Paper: `prop:time`, paper/paper.tex: the coefficient stage costs one coefficient
evaluation and a polynomial overhead per closed walk, and the child input is read once.

All the parameters, the call word, the number of rounds `S` and the prefix are polynomially bounded on a dispatched
call (`Cells.dispatched_parametersWord_length`, `Program.callWord_length_le`, `Greedy.seedRounds_le`); the size
`Y = |callWord| + |parametersWord| + S + 10` collects them (`gammaSizes`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3200000

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicGates.Close.Interfaces (Call callWord listWord)
open NearQuarticWires.Program NearQuarticWires.Greedy

variable {B1 B2 : ℕ}

/-- The size collecting the call word, the parameters and the number of rounds. -/
noncomputable def gammaY (q : ChildRequest B1 B2) : ℕ :=
  (callWord q.call).length + (parametersWord q.selected.1).length + q.selected.1.S + 10

/-- The sizes of a child evaluation. -/
structure GammaSizes (q : ChildRequest B1 B2) : Prop where
  k : q.selected.1.k ≤ q.selected.1.S
  ellf : q.selected.1.ellf ≤ q.selected.1.S
  pi : q.seedPrefix.length ≤ q.selected.1.S
  n : q.call.n ≤ (callWord q.call).length
  words : (params6 q.selected.1).flatMap natWord ++ natWord q.selected.1.k ++
    (params10 q.selected.1).flatMap natWord ++ natWord q.selected.1.Q ++ natWord q.selected.1.ellf ++
    (((StageLift.parameterHeadScalars q.selected.1).drop 19).flatMap natWord ++
      listWord natWord (q.selected.1.primes.sort (· ≤ ·)) ++ (StageLift.parameterTailScalars q.selected.1).flatMap natWord ++
      listWord natWord q.selected.1.factors) = parametersWord q.selected.1

theorem gammaSizes (q : ChildRequest B1 B2) : GammaSizes q := by
  have hr := Cells.prepare_spec _ q.selected.1 q.selected.2
  have hS : q.selected.1.S = 2 * q.selected.1.m * q.selected.1.ellf := hr.S_eq
  have hm : q.selected.1.m = 4 := hr.m_eq
  have he : q.selected.1.ellf = max q.selected.1.k (q.selected.1.Qexp + 1) := hr.ellf_eq
  refine ⟨?_, ?_, ?_, Cells.dispatched_n_le_callWord q.dispatched, ?_⟩
  · rw [hS, hm, he]; have := le_max_left q.selected.1.k (q.selected.1.Qexp + 1); omega
  · rw [hS, hm]; omega
  · have := q.prefix_le; rwa [seedLength_runCall] at this
  · rw [parametersWord_split, List.append_assoc ((params19 q.selected.1).flatMap natWord), paramsTail_layout]
    simp [params19, params6, params10, List.append_assoc]


theorem natListCost_le (xs : List ℕ) (P : ℕ) (h : (listWord natWord xs).length ≤ P) :
    natListCost xs ≤ 230 * (P + 2) * P := by
  have hc := listWord_count natWord xs natWord_pos
  have := skipListCost_le natWord (fun x => 20 * natBitLength x + 20) xs 20 P natWord_pos (by omega)
    (fun x hx => by
      have h1 := natCost_le x
      have h2 : 1 ≤ (natWord x).length := natWord_pos x
      nlinarith)
  unfold natListCost
  calc _ ≤ (20 + 210) * (P + 2) * (listWord natWord xs).length := this
    _ ≤ 230 * (P + 2) * P := Nat.mul_le_mul_left _ h

/-- **The cost of the coefficient stage, in the size `Y`.** -/
theorem gammaRunCost_le (q : ChildRequest B1 B2) (B : ℕ)
    (hγ : ∀ x ∈ gammaTable q, (NearCubicGates.Close.Interfaces.intWord x).length ≤ B + 1) :
    gammaRunCost q B ≤ 100000 * ((2 ^ (q.selected.1.k / 2 * 8) + 1) * (B + gammaY q ^ 2) + (childInput q).length + 1) := by
  have hz := gammaSizes q
  have hP := congrArg List.length hz.words
  simp only [List.length_append] at hP
  have hw := congrArg List.length (childInput_fields q)
  simp only [seedPre, tailWord, List.length_append, List.length_cons, List.length_nil] at hw
  have hfr : ∀ u : List Bool, (frame u).length = 2 * u.length + 1 := fun u => by
    rw [NearCubicGates.Close.Codec.frame_eq_marks]; simp [marks_length]
  rw [hfr, hfr, hfr] at hw
  have hYdef : gammaY q = (callWord q.call).length + (parametersWord q.selected.1).length + q.selected.1.S + 10 := rfl
  have hkS := hz.k
  have hπS := hz.pi
  have hnL := hz.n
  have hkhS : q.selected.1.k / 2 ≤ q.selected.1.S := by omega
  -- the read
  have hread := readCost_le q.call (params6 q.selected.1) q.selected.1.k
  have hΛ := natBitLength_le_self_succ ((callWord q.call).length + q.call.n)
  have hr1 : 440 * (natBitLength ((callWord q.call).length + q.call.n) + 2) * ((callWord q.call).length + 1) ≤ 880 * (gammaY q * gammaY q) := by
    have : (natBitLength ((callWord q.call).length + q.call.n) + 2) * ((callWord q.call).length + 1) ≤ (2 * gammaY q) * gammaY q :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hr2 : (q.selected.1.k + 3) * (80 * q.selected.1.k + 120) ≤ 80 * (gammaY q * gammaY q) := by
    have : (q.selected.1.k + 3) * (80 * q.selected.1.k + 120) ≤ (gammaY q * (80 * gammaY q)) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hn1 := natsCost_le (params10 q.selected.1)
  have hkb := natBitLength_le_self_succ (q.selected.1.k / 2)
  have hr3 : (natBitLength (q.selected.1.k / 2) + 10) * (100 * (q.selected.1.k / 2) + 200) ≤
      100 * (gammaY q * gammaY q) + 3000 * gammaY q + 2000 := by
    have : (natBitLength (q.selected.1.k / 2) + 10) * (100 * (q.selected.1.k / 2) + 200) ≤ (gammaY q + 10) * (100 * gammaY q + 200) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  -- the rest of the parameters
  have hn2 := natsCost_le ((StageLift.parameterHeadScalars q.selected.1).drop 19)
  have hn3 := natsCost_le (StageLift.parameterTailScalars q.selected.1)
  have hl1 := natListCost_le (q.selected.1.primes.sort (· ≤ ·)) (parametersWord q.selected.1).length (by omega)
  have hl2 := natListCost_le q.selected.1.factors (parametersWord q.selected.1).length (by omega)
  have hl3 : 230 * ((parametersWord q.selected.1).length + 2) * (parametersWord q.selected.1).length ≤ 230 * (gammaY q * gammaY q) := by
    have : ((parametersWord q.selected.1).length + 2) * (parametersWord q.selected.1).length ≤ gammaY q * gammaY q := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  -- the prefix
  have hπb := natBitLength_le_self_succ q.seedPrefix.length
  have hp1 : (natBitLength q.seedPrefix.length + 10) * (100 * q.seedPrefix.length + 200) ≤
      100 * (gammaY q * gammaY q) + 3000 * gammaY q + 2000 := by
    have : (natBitLength q.seedPrefix.length + 10) * (100 * q.seedPrefix.length + 200) ≤
        (gammaY q + 10) * (100 * gammaY q + 200) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hp2 : q.seedPrefix.length ^ 2 ≤ gammaY q * gammaY q := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  -- the fixed part of the requests
  have hhw : (headWord q.selected.1.ellf (q.selected.1.k / 2) q.selected.1.Q q.seedPrefix).length ≤ 5 * gammaY q := by
    have h1 := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length q.seedPrefix.length
    have h2 := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length
      (Algorithm.CellCall.prefixValue q.seedPrefix)
    have h4 := natBitLength_le_of_lt_pow (E := q.seedPrefix.length + 1) (by omega)
      (lt_trans (Greedy.prefixValue_lt q.seedPrefix) (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    have h5 : (natWord (q.selected.1.k / 2)).length ≤ (natWord q.selected.1.k).length := by
      rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length,
        NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]
      have := natBitLength_mono (show q.selected.1.k / 2 ≤ q.selected.1.k by omega); omega
    simp only [headWord, seedWord, List.length_append]; omega
  have hkh2 : (q.selected.1.k / 2) ^ 2 ≤ gammaY q * gammaY q := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  -- the table
  have hU : (listWord NearCubicGates.Close.Interfaces.intWord (gammaTable q)).length ≤
      16 * gammaY q + 3 + (2 ^ (q.selected.1.k / 2 * 8) * B + 2 ^ (q.selected.1.k / 2 * 8)) := by
    have hlen : (gammaTable q).length = 2 ^ (q.selected.1.k / 2 * 8) := by
      rw [gammaTable, List.length_map, walkList_len]; rfl
    have hsum := sum_map_le (gammaTable q) (fun x => (NearCubicGates.Close.Interfaces.intWord x).length)
      (fun _ => B + 1) hγ
    have hN := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length (gammaTable q).length
    have hNb : natBitLength (gammaTable q).length ≤ q.selected.1.k / 2 * 8 + 1 := by
      rw [hlen]; exact natBitLength_le_of_lt_pow (by omega) (Nat.pow_lt_pow_right (by norm_num) (by omega))
    simp only [listWord, List.length_append, List.length_flatMap]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, hlen] at hsum
    have : 2 ^ (q.selected.1.k / 2 * 8) * (B + 1) = 2 ^ (q.selected.1.k / 2 * 8) * B + 2 ^ (q.selected.1.k / 2 * 8) := by
      ring
    omega
  have hN1 : 1 ≤ 2 ^ (q.selected.1.k / 2 * 8) := Nat.one_le_two_pow
  have hY1 : 10 ≤ gammaY q := by omega
  -- one walk
  have hwc : walkCost (headWord q.selected.1.ellf (q.selected.1.k / 2) q.selected.1.Q q.seedPrefix).length (q.selected.1.k / 2) (16 * (q.selected.1.k / 2) + 8)
      (reqLen q.selected.1.ellf (q.selected.1.k / 2) q.selected.1.Q q.seedPrefix) B + 7 ≤ 5000 * (B + gammaY q * gammaY q) := by
    have hY10 : 10 * gammaY q ≤ gammaY q * gammaY q := Nat.mul_le_mul_right _ hY1
    unfold walkCost requestCost callCost cleanCost reqLen
    linarith [hhw, hkh2, hY1, hkhS, hY10]
  have hmul : 2 ^ (q.selected.1.k / 2 * 8) * (walkCost (headWord q.selected.1.ellf (q.selected.1.k / 2) q.selected.1.Q q.seedPrefix).length
      (q.selected.1.k / 2) (16 * (q.selected.1.k / 2) + 8) (reqLen q.selected.1.ellf (q.selected.1.k / 2) q.selected.1.Q q.seedPrefix) B + 7) ≤
      5000 * (2 ^ (q.selected.1.k / 2 * 8) * B) + 5000 * (2 ^ (q.selected.1.k / 2 * 8) * (gammaY q * gammaY q)) := by
    have := Nat.mul_le_mul_left (2 ^ (q.selected.1.k / 2 * 8)) hwc
    nlinarith
  have hYY : gammaY q ≤ gammaY q * gammaY q := Nat.le_mul_self _
  have hN8Y : 2 ^ (q.selected.1.k / 2 * 8) ≤ 2 ^ (q.selected.1.k / 2 * 8) * (gammaY q * gammaY q) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
  have hY10 : 10 * gammaY q ≤ gammaY q * gammaY q := Nat.mul_le_mul_right _ hY1
  -- the sum
  have hA : seedHeadCost q.call (params6 q.selected.1) (params10 q.selected.1) q.selected.1.k q.selected.1.Q q.selected.1.ellf ≤
      3000 * (gammaY q * gammaY q) := by
    unfold seedHeadCost
    linarith only [hread, hr1, hr2, hr3, hn1, hP, hkS, hYdef, hY10, hY1]
  have hB : tailCost ((StageLift.parameterHeadScalars q.selected.1).drop 19) (q.selected.1.primes.sort (· ≤ ·))
      (StageLift.parameterTailScalars q.selected.1) q.selected.1.factors
      (witnessPrefix q.call q.selected.1 q.witness) (certifiedBits (runCall q.call q.selected q.witness)) ≤
      1000 * (gammaY q * gammaY q) + 10 * (childInput q).length := by
    unfold tailCost
    linarith only [hn2, hn3, hl1, hl2, hl3, hP, hw, hYdef, hY10, hY1]
  have hC : prefixCost q.seedPrefix.length ≤ 1000 * (gammaY q * gammaY q) := by
    unfold prefixCost
    linarith only [hp1, hp2, hπS, hYdef, hY10, hY1]
  have hD : walkStartCost (q.selected.1.k / 2) (2 * (headWord q.selected.1.ellf (q.selected.1.k / 2) q.selected.1.Q q.seedPrefix).length) ≤
      1000 * (gammaY q * gammaY q) := by
    unfold walkStartCost tableCost
    linarith only [hhw, hkhS, hYdef, hY10, hY1]
  have hR : 100000 * ((2 ^ (q.selected.1.k / 2 * 8) + 1) * (B + gammaY q ^ 2) + (childInput q).length + 1) =
      100000 * (2 ^ (q.selected.1.k / 2 * 8) * B) + 100000 * (2 ^ (q.selected.1.k / 2 * 8) * (gammaY q * gammaY q)) + 100000 * B +
        100000 * (gammaY q * gammaY q) + 100000 * (childInput q).length + 100000 := by ring
  rw [hR]
  have hH : headCost q.call (params6 q.selected.1) (params10 q.selected.1)
      ((StageLift.parameterHeadScalars q.selected.1).drop 19) (q.selected.1.primes.sort (· ≤ ·))
      (StageLift.parameterTailScalars q.selected.1) q.selected.1.factors q.selected.1.k q.selected.1.Q q.selected.1.ellf
      (witnessPrefix q.call q.selected.1 q.witness) (certifiedBits (runCall q.call q.selected q.witness)) q.seedPrefix
      (childInput q) ≤ 6000 * (gammaY q * gammaY q) + 100 * (childInput q).length + 100 := by
    unfold headCost
    linarith only [hA, hB, hC, hD]
  unfold gammaRunCost gammaCost
  linarith only [hH, hmul, hU, hN8Y, hYdef, hY10, hY1, hN1, Nat.zero_le (2 ^ (q.selected.1.k / 2 * 8) * B),
    Nat.zero_le (2 ^ (q.selected.1.k / 2 * 8) * (gammaY q * gammaY q)), Nat.zero_le (gammaY q * gammaY q), Nat.zero_le B,
    Nat.zero_le (childInput q).length]

end NearQuarticWires.Control
