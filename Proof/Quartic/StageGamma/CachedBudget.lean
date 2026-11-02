import Proof.Quartic.StageGamma.CachedDecode

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: retaining the
ORIGINAL request adds only its actual serialized length and the degree. -/
theorem cachedRequestBudget_eq (request : Machine.GammaRequest) :
    cachedRequestBudget request = 4 * cachedFieldCost request +
      300 * ((Machine.gammaRequestWord request).length + request.parameters.ell + 1) + 2 := by
  simp only [cachedRequestBudget, retainedCost, cachedFieldCost, SignedSortKey.binary_length]
  ring

/-- `prop:time`, paper/paper.tex: the complete
cold retained-input field stage pays its physical input copies as well as
its once-only search, within the exact ORIGINAL coefficient census. -/
theorem cachedRequestBudget_selected_le {B1 B2 : ℕ} (q : Greedy.ChildRequest B1 B2)
    (w : Cycle.Walk q.cellCall.seed.N Algorithm.traceOrder) :
    cachedRequestBudget (Greedy.gammaRequest q w) ≤
      (10 ^ 16 * (TSK fieldProducerCallee + 1)) *
        ((q.selected.1.Q + 1) ^ 8 *
          (Cycle.seedLength (Greedy.gammaRequest q w).parameters + 9) ^ 4) := by
  let request := Greedy.gammaRequest q w
  let S := Cycle.seedLength request.parameters
  let Z := (q.selected.1.Q + 1) ^ 8 * (S + 9) ^ 4
  have hf := cachedFieldCost_selected_le q w
  have hi := gammaRequestWord_length_le request
  have hell : request.parameters.ell ≤ S := by dsimp [S, Cycle.seedLength]; omega
  have hpow : S + 9 ≤ (S + 9) ^ 4 := by
    calc
      _ = (S + 9) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hZ : (S + 9) ^ 4 ≤ Z := Nat.le_mul_of_pos_left _ (by positivity)
  have h1 : 1 ≤ Z := by
    have hh : 1 ≤ (S + 9) ^ 4 := Nat.one_le_pow _ _ (by omega)
    exact hh.trans hZ
  have hSZ : S + 9 ≤ Z := hpow.trans hZ
  change cachedFieldCost request ≤ (16 * (10 ^ 13 * (TSK fieldProducerCallee + 1))) * Z at hf
  rw [cachedRequestBudget_eq]
  change _ ≤ (10 ^ 16 * (TSK fieldProducerCallee + 1)) * Z
  have hZK : Z ≤ (TSK fieldProducerCallee + 1) * Z := Nat.le_mul_of_pos_left _ (by omega)
  nlinarith

end NearQuarticWires.StageGamma
