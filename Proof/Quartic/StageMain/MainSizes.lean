import Proof.Quartic.StageMain.MainCapacity
import Proof.Quartic.StageMain.MainWordFunction

/-!
# Fixed arity-header sizes for the complete main machine

`prop:time`, paper/paper.tex, bounds finite
arithmetic and call work polynomially in the original arity. The raw
leading tag and arity word determine all three reservations here;
the exponentially long certificate suffix never determines their width.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Controller Bounds

def mainSizeCoefficient (B1 K : ℕ) : ℕ := 1000000000 * (coefficient B1 K) ^ 2

def mainSizeDegree (B1 B2 d : ℕ) : ℕ := 2 * degree B1 B2 d

def mainSizes (B1 B2 K d : ℕ) : Sz :=
  ⟨mainSizeCoefficient B1 K, mainSizeDegree B1 B2 d,
   mainSizeCoefficient B1 K, mainSizeDegree B1 B2 d,
   mainSizeCoefficient B1 K, mainSizeDegree B1 B2 d⟩

theorem mainSizes_min (B1 B2 K d L : ℕ) : 64 ≤ (mainSizes B1 B2 K d).W L := by
  have hc : 1 ≤ coefficient B1 K := by unfold coefficient; omega
  have hsq : 1 ≤ (coefficient B1 K) ^ 2 := Nat.pow_pos hc
  have hp : 1 ≤ 2 ^ (mainSizeDegree B1 B2 d * L) := Nat.one_le_two_pow
  unfold mainSizes Sz.W mainSizeCoefficient
  nlinarith

theorem mainSizes_arity (B1 B2 K d n : ℕ) :
    1000000000 * (envelope B1 B2 K d n) ^ 2 ≤
      (mainSizes B1 B2 K d).W (1 + natBitLength n) := by
  have hn : n + 1 ≤ 2 ^ (1 + natBitLength n) := by
    have hlt := lt_natBitLength n
    have he := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (show natBitLength n ≤ 1 + natBitLength n by omega)
    omega
  have hh := Nat.pow_le_pow_left hn (2 * degree B1 B2 d)
  calc
    _ = (n + 1) ^ (2 * degree B1 B2 d) * mainSizeCoefficient B1 K := by
      have heq (a x e : ℕ) : 1000000000 * (a * x ^ e) ^ 2 =
          x ^ (2 * e) * (1000000000 * a ^ 2) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm e 2]
        ring
      exact heq _ _ _
    _ ≤ (2 ^ (1 + natBitLength n)) ^ (2 * degree B1 B2 d) * mainSizeCoefficient B1 K :=
      Nat.mul_le_mul_right _ hh
    _ = _ := by
      simp only [mainSizes, Sz.W, mainSizeDegree, ← pow_mul]
      rw [Nat.mul_comm (1 + natBitLength n)]

noncomputable def mainStepLimit (B1 B2 K d : ℕ) (c : Call) (w : List Bool) : ℕ :=
  100 * (mainSizes B1 B2 K d).W (leadOnes (cachedMainWord B1 B2 c w))

theorem mainSizes_capacity {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ)
    (hb : ∀ r, budget r ≤ K * (r.call.n + 1) ^ d)
    (c : Call) (w : List Bool) (p : Program.Selected c) (hd : Program.dispatch B1 B2 c = some p) :
    let l := leadOnes (cachedMainWord B1 B2 c w)
    ActiveCapacity f hd w ((mainSizes B1 B2 K d).W l)
      ((mainSizes B1 B2 K d).Lk l) ((mainSizes B1 B2 K d).Bk l) (mainStepLimit B1 B2 K d c w) := by
  have hhead : leadOnes (cachedMainWord B1 B2 c w) = 1 + natBitLength c.n :=
    dispatched_greedy_header_width hd w (mainFieldBits B1 B2 c)
  exact activeCapacity_of_envelope f K d hb hd w _ (by rw [hhead]; exact mainSizes_arity B1 B2 K d c.n)

noncomputable def mainBudgetWithEntry {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ) : Call → List Bool → ℕ :=
  mainBudgetOf f (mainSizes B1 B2 K d) (mainStepLimit B1 B2 K d)

noncomputable def main_of_entry_bound {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ)
    (hb : ∀ r, budget r ≤ K * (r.call.n + 1) ^ d) :
    WordFunction (Call × List Bool) (fun r => Program.greedyWord B1 B2 r.1 r.2)
      (fun r => frame (Program.mainWord B1 B2 r.1 r.2))
      (fun r => mainBudgetWithEntry f K d r.1 r.2) :=
  mainWordFunction_of_bounds f (mainSizes B1 B2 K d) (mainStepLimit B1 B2 K d)
    (fun _ _ => mainSizes_min B1 B2 K d _) (mainSizes_capacity f K d hb)

end NearQuarticWires.StageMain
