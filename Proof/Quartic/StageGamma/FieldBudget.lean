import Proof.Quartic.StageGamma.FieldProducer
import Proof.Gates.CounterMachine.PrefixFinal
import Proof.Quartic.Cells.ParametersGammaSetup

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.CounterMachine.PrefixProg

/-- `prop:time`, paper/paper.tex: the ORIGINAL
request contains fourteen binary fields, all of seed-polynomial length. -/
theorem gammaRequestWord_length_le (request : Machine.GammaRequest) :
    (Machine.gammaRequestWord request).length ≤
      42 * (Cycle.seedLength request.parameters + 1) := by
  rw [← requestFields_word]
  have hh : ∀ x ∈ requestFields request,
      (natWord x).length ≤ 3 * (Cycle.seedLength request.parameters + 1) := by
    intro x hx
    rw [natWord_length]
    have := requestFields_bitLength request x hx
    omega
  have hgen : ∀ vs : List ℕ,
      (∀ x ∈ vs, (natWord x).length ≤ 3 * (Cycle.seedLength request.parameters + 1)) →
      (List.flatMap natWord vs).length ≤
        vs.length * (3 * (Cycle.seedLength request.parameters + 1)) := by
    intro vs
    induction vs with
    | nil => intro _; simp
    | cons v vs ih =>
      intro h
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hv := h v (by simp)
      have ht := ih (fun x hx => h x (by simp [hx]))
      nlinarith
  have hl := hgen (requestFields request) hh
  rw [requestFields_length] at hl
  nlinarith

/-- `prop:time`, paper/paper.tex: the degree
producer's fixed compiler overhead is polynomial in the actual seed. -/
theorem fieldProducerCost_le (request : Machine.GammaRequest) :
    fieldProducerCost request ≤
      (10 ^ 12 * (TSK fieldProducerCallee + 1)) *
        (Cycle.seedLength request.parameters + 9) ^ 4 := by
  let s := Cycle.seedLength request.parameters
  have hell : request.parameters.ell ≤ s := by dsimp [s, Cycle.seedLength]; omega
  have hl : leadOnes (Machine.gammaRequestWord request) =
      natBitLength request.parameters.ell := by
    unfold Machine.gammaRequestWord
    simp only [List.append_assoc]
    exact leadOnes_natWord _ _
  have hp := pow_nbl_le request.parameters.ell
  have hb := nbl_le_self' request.parameters.ell
  have hi := gammaRequestWord_length_le request
  have hp' : 2 ^ natBitLength request.parameters.ell ≤ 2 * (s + 9) := by omega
  have hb' : natBitLength request.parameters.ell ≤ s + 9 := by omega
  have hi' : (Machine.gammaRequestWord request).length ≤ 42 * (s + 9) := by omega
  let F (L P I : ℕ) : ℕ :=
    (30 * L + 20) + 256 + (L * (60 * (P * 64) + 19) + 7 * L + 3) +
      (L * 8 + 7 * L + 3) + (L * 8 + 7 * L + 3) + 9 + 12 + 10 + 1 +
      (130 * (50 * (P * 64) + 11) + 20 + 10 + 130 + 3 + 1 +
        (3 * L + 1 + (3 * (P * 64) + 1) + 1 + 1 + 10 + 4)) + 1 +
      (500 * (s + 9) * (500 * (P * 64 + 1) ^ 2 +
        100 * (TSK fieldProducerCallee + 3)) + 1 +
        (10 * I + 5 * (500 * (s + 9)) + 15 +
          10 * (5 * ((2 * (P * 64) + 1) * (500 * (s + 9))) + 2) + 10))
  have he : fieldProducerCost request = F (natBitLength request.parameters.ell)
      (2 ^ natBitLength request.parameters.ell) (Machine.gammaRequestWord request).length := by
    simp only [fieldProducerCost, langBudget, hl, fieldProducerSizes, Sz.W, Sz.Lk, Sz.Bk,
      one_mul, Nat.zero_mul, pow_zero, mul_zero, costA, costB, costC, VV, MM, F, s]
    ring
  rw [he]
  calc
    _ ≤ F (s + 9) (2 * (s + 9)) (42 * (s + 9)) := by
      dsimp [F]
      gcongr
    _ ≤ _ := by
      have h1 : s + 9 ≤ (s + 9) ^ 4 := by
        calc
          _ = (s + 9) ^ 1 := (pow_one _).symm
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
      have h2 : (s + 9) ^ 2 ≤ (s + 9) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
      have h3 : (s + 9) ^ 3 ≤ (s + 9) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
      have ht := Nat.mul_le_mul_left (TSK fieldProducerCallee) h1
      have h4 : 1 ≤ (s + 9) ^ 4 := Nat.one_le_pow _ _ (by omega)
      dsimp [F]
      nlinarith

/-- `prop:time`, paper/paper.tex: this is the
complete once-only clock from the original request to the cached modulus. -/
noncomputable def cachedFieldCost (request : Machine.GammaRequest) : ℕ :=
  4 * fieldProducerCost request + 4 * unaryFieldCost request + 12

/-- `prop:time`, paper/paper.tex: the complete
once-only primitive setup includes every ORIGINAL-source parsing charge. -/
theorem cachedFieldCost_le (request : Machine.GammaRequest) :
    cachedFieldCost request ≤ (10 ^ 13 * (TSK fieldProducerCallee + 1)) *
      (2 ^ (2 * request.parameters.ell) *
        (Cycle.seedLength request.parameters + 9) ^ 4) := by
  have hp := fieldProducerCost_le request
  have hu := unaryFieldCost_le request
  let q := Cycle.seedLength request.parameters + 9
  let p := 2 ^ (2 * request.parameters.ell)
  have h1 : q ≤ q ^ 4 := by
    calc
      _ = q ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by dsimp [q]; omega) (by decide)
  have h2 : q ^ 4 ≤ p * q ^ 4 := Nat.le_mul_of_pos_left _ (by dsimp [p]; positivity)
  have h3 : p * q ≤ p * q ^ 4 := Nat.mul_le_mul_left p h1
  have h4 : 1 ≤ p * q ^ 4 := by
    have hq : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by dsimp [q]; omega)
    exact hq.trans h2
  have h5 := Nat.mul_le_mul_left (10 ^ 12 * (TSK fieldProducerCallee + 1)) h2
  dsimp only [cachedFieldCost]
  change _ ≤ (10 ^ 13 * (TSK fieldProducerCallee + 1)) * (p * q ^ 4)
  change fieldProducerCost request ≤ (10 ^ 12 * (TSK fieldProducerCallee + 1)) * q ^ 4 at hp
  change unaryFieldCost request ≤ 1000 * (p * q) at hu
  nlinarith

/-- `prop:time`, paper/paper.tex: on every actual
greedy call, the one cached field search is covered by the exact
`(Q+1)^8` coefficient census and a seed-polynomial factor. -/
theorem cachedFieldCost_selected_le {B1 B2 : ℕ} (q : Greedy.ChildRequest B1 B2)
    (w : Cycle.Walk q.cellCall.seed.N Algorithm.traceOrder) :
    cachedFieldCost (Greedy.gammaRequest q w) ≤
      (16 * (10 ^ 13 * (TSK fieldProducerCallee + 1))) *
        ((q.selected.1.Q + 1) ^ 8 *
          (Cycle.seedLength (Greedy.gammaRequest q w).parameters + 9) ^ 4) := by
  have hh := cachedFieldCost_le (Greedy.gammaRequest q w)
  have hf := Cells.gammaRequest_field_search_bound q w
  calc
    _ ≤ (10 ^ 13 * (TSK fieldProducerCallee + 1)) *
        ((16 * (q.selected.1.Q + 1) ^ 8) *
          (Cycle.seedLength (Greedy.gammaRequest q w).parameters + 9) ^ 4) := by
      exact hh.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hf))
    _ = _ := by ring

end NearQuarticWires.StageGamma
