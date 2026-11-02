import Proof.Quartic.StageCertTests.Transpose
import Proof.Quartic.StageCertTests.CropOrder
import Proof.Wire_3_5.StarPartition

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.TabMachine

/-- `imp:partition` and `prop:time`, paper/paper.tex: the native square padding costs at most twice the
exact original center census. -/
theorem native_square_le_two_centers (P : StarParams) :
    (2 ^ P.leftCenterBits)^2 ≤ 2 * 2 ^ (P.n-P.k) := by
  have hb := P.centerBits_balanced
  calc
    (2 ^ P.leftCenterBits)^2 = 2 ^ (2*P.leftCenterBits) := by rw [←pow_mul];congr 1;omega
    _ ≤ 2 ^ (1+(P.leftCenterBits+P.rightCenterBits)) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    _ = 2 * 2 ^ (P.n-P.k) := by rw [pow_add,P.centerBits_sum];norm_num

/-- `imp:printer` and `lem:print`, paper/paper.tex: a fixed number of complete equal-length native rows
is a single contiguous prefix of the flattened physical table. -/
theorem take_flatten_uniform {α : Type*} (R C : ℕ) (rows : List (List α))
    (hrows : ∀ row ∈ rows, row.length = R) (hC : C ≤ rows.length) :
    rows.flatten.take (C*R) = (rows.take C).flatten := by
  induction C generalizing rows with
  | zero => simp
  | succ C ih =>
    cases rows with
    | nil => simp at hC
    | cons row rows =>
      have hr : row.length = R := hrows row (by simp)
      have ht : ∀ r ∈ rows, r.length = R := fun r h => hrows r (by simp [h])
      have hc : C ≤ rows.length := by simpa using hC
      simp only [List.flatten_cons,List.take_succ_cons,Nat.succ_mul]
      rw [Nat.add_comm (C*R) R,←hr,List.take_length_add_append,hr,ih rows ht hc]

/-- `imp:printer` and `lem:print`, paper/paper.tex: retaining the valid outer half of a native square
needs only one prefix scan and keeps every inner-half coordinate. -/
theorem native_prefix_rows {α : Type*} (U C : ℕ) (hC : C ≤ U)
    (f : Fin U → Fin U → α) :
    ((List.ofFn fun i => List.ofFn fun j => f i j).flatten).take (U*C) =
      (List.ofFn fun i : Fin C => List.ofFn fun j : Fin U => f (i.castLE hC) j).flatten := by
  rw [Nat.mul_comm U C,take_flatten_uniform U C _
    (by intro row hr;obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr;exact List.length_ofFn)
    (by simpa using hC),take_ofFn_castLE _ hC]

/-- `imp:partition` and `lem:print`, paper/paper.tex: the transposed raw cuts print the exact low-row/high-column
table in a contiguous native prefix, without a table permutation. -/
theorem native_prefix_transposed_table (r : NearCubicWires.RepairOrdinary.MatrixScoreBatch.Request)
    (C : ℕ) (hC : C ≤ r.U) :
    (pvals false (StagePrint.cutTable (transposeRequest r))).take (r.U*C) =
      (List.ofFn fun high : Fin C => List.ofFn fun low : Fin r.U =>
        StagePrint.cutTable r low (high.castLE hC)).flatten := by
  have ht : StagePrint.cutTable (transposeRequest r) = fun i j => StagePrint.cutTable r j i := by
    funext i j
    exact transposeRequest_table r i j
  rw [ht]
  exact native_prefix_rows r.U C hC (fun i j => StagePrint.cutTable r j i)

end NearQuarticWires.StageCertTests
