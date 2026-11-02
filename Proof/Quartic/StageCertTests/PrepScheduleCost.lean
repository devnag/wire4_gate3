import Proof.Quartic.StageCertTests.PreparedSourceCost
import Proof.Gates.CellsPack.Lang

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.CellsPack (Gof)

variable {B1 B2 : ℕ}

/-- `prop:time`, paper/paper.tex:
the actual direct-source arity header has polynomial size in
the original call and excludes every native table census. -/
theorem PreparedPolynomial.header : PreparedPolynomial (B1 := B1) (B2 := B2)
    (fun r => leadOnes r.word) := by
  refine ((PreparedPolynomial.const 1).add PreparedPolynomial.arityBits).mono ?_
  intro r
  rw [r.word_eq]
  have h := StageMain.taggedCall_header_width r.call
    (Program.parametersWord r.selected.1 ++ frame (Program.witnessPrefix r.call r.selected.1 r.witness))
  simpa only [List.append_assoc] using h.le

/-- `prop:time`, paper/paper.tex:
the actual initialized arithmetic width is polynomial in the
original call word, with no native output reserve. -/
theorem PreparedPolynomial.workspace : PreparedPolynomial (B1 := B1) (B2 := B2)
    (fun r => (prepScheduleSizes B1 B2).W (leadOnes r.word)) := by
  let z := prepScheduleSizes B1 B2
  let D := prepScheduleDegree B1 B2
  refine ⟨z.a1*4^D,D,fun r => ?_⟩
  have hhead : leadOnes r.word = 1+natBitLength r.call.n := by
    rw [r.word_eq]
    simpa only [List.append_assoc] using StageMain.taggedCall_header_width r.call
      (Program.parametersWord r.selected.1 ++ frame (Program.witnessPrefix r.call r.selected.1 r.witness))
  have hbits := NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le r.call.n
  have hbase : 2*2^natBitLength r.call.n ≤ 4*(r.call.n+1) := by omega
  have halg (d b a : ℕ) : 2^(d*(1+b))*a = (2*2^b)^d*a := by
    rw [Nat.mul_comm d (1+b),Nat.pow_mul,Nat.pow_add,pow_one]
  have hwidth : z.W (leadOnes r.word) ≤ z.a1*4^D*(r.call.n+1)^D := by
    change 2^(D*leadOnes r.word)*z.a1 ≤ _
    rw [hhead,halg]
    calc
      (2*2^natBitLength r.call.n)^D*z.a1 ≤ (4*(r.call.n+1))^D*z.a1 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbase D)
      _ = _ := by rw [mul_pow];ring
  exact hwidth.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Cells.dispatched_n_le_callWord r.dispatched) 1) D))

/-- `prop:time`, paper/paper.tex:
all compilation setup factors are polynomial original-source
quantities for this empty-callee scheduling program. -/
theorem PreparedPolynomial.compilationScale_of (z : Sz) (K : Callee)
    (hW : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r => z.W (leadOnes r.word)))
    (hH : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r => leadOnes r.word))
    (hLk : ∀ n, z.Lk n = 0) (hBk : ∀ n, z.Bk n = 0) :
    PreparedPolynomial (B1 := B1) (B2 := B2) (fun r => Gof K z (leadOnes r.word)) := by
  simp only [Gof,hLk,hBk,Nat.add_zero]
  exact (((((((((hW.add hH).add (PreparedPolynomial.const z.a1)).add
    (PreparedPolynomial.const z.a2)).add (PreparedPolynomial.const z.a3)).add
      (PreparedPolynomial.const z.c1)).add (PreparedPolynomial.const z.c2)).add
        (PreparedPolynomial.const z.c3)).add (PreparedPolynomial.const (TSK K))).add
          (PreparedPolynomial.const 1))

/-- `prop:time`, paper/paper.tex:
the actual direct-source allocator satisfies every polynomial
compilation-scale bound without a native-table reserve. -/
theorem PreparedPolynomial.compilationScale : PreparedPolynomial (B1 := B1) (B2 := B2)
    (fun r => Gof StageRecovery.packetCallee (prepScheduleSizes B1 B2) (leadOnes r.word)) :=
  PreparedPolynomial.compilationScale_of (prepScheduleSizes B1 B2) StageRecovery.packetCallee
    PreparedPolynomial.workspace PreparedPolynomial.header
    (by intro n;simp [prepScheduleSizes,Sz.Lk]) (by intro n;simp [prepScheduleSizes,Sz.Bk])

/-- `prop:time`, paper/paper.tex:
the complete actual compiled original-preparation scheduler has
polynomial cost, including cold initialization, every original source
bit, parameter decoding, threshold powers and final head returns. -/
theorem PreparedPolynomial.compiledBudget : PreparedPolynomial (B1 := B1) (B2 := B2)
    (fun r => r.budget) := by
  have hN := PreparedPolynomial.sourceSteps (B1 := B1) (B2 := B2)
  have hG := PreparedPolynomial.compilationScale (B1 := B1) (B2 := B2)
  have hI := PreparedPolynomial.inputLength (B1 := B1) (B2 := B2)
  have hupper : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r =>
      10^6*((prepScheduleSteps r.call r.selected.1+1)*
        (Gof StageRecovery.packetCallee (prepScheduleSizes B1 B2) (leadOnes r.word))^2)+10*r.word.length) :=
    ((PreparedPolynomial.const (10^6)).mul ((hN.add (PreparedPolynomial.const 1)).mul (hG.pow 2))).add
      ((PreparedPolynomial.const 10).mul hI)
  refine hupper.mono ?_
  intro r
  exact NearCubicGates.Close.CellsPack.lang_le2 StageRecovery.packetCallee (prepScheduleSizes B1 B2)
    r.word (prepScheduleSteps r.call r.selected.1)

/-- `sec:algorithm`, paper/paper.tex:
the direct scheduler cost is zero off dispatch and is the actual
cold compiled budget on the selected branch. -/
noncomputable def prepScheduleBudget (B1 B2 : ℕ) (c : Call) (w : List Bool) : ℕ :=
  match hd : Program.dispatch B1 B2 c with
  | none => 0
  | some p => (PreparedScheduleRequest.mk c w p hd).budget

/-- `prop:time`, paper/paper.tex:
the exact direct source-to-metadata machine budget is polynomial
in the actual original call word on every call and witness. -/
theorem prepScheduleCost (B1 B2 : ℕ) : Program.PolyCost (prepScheduleBudget B1 B2) := by
  obtain ⟨K,e,hK⟩ := PreparedPolynomial.compiledBudget (B1 := B1) (B2 := B2)
  refine ⟨K,e,fun c w => ?_⟩
  unfold prepScheduleBudget
  split
  · exact Nat.zero_le _
  · rename_i p hd
    exact hK (PreparedScheduleRequest.mk c w p hd)

end NearQuarticWires.StageCertTests
