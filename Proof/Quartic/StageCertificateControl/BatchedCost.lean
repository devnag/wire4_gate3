import Proof.Quartic.StageCertificateControl.BatchedMachine
import Proof.Quartic.Control.GammaControl

/-!
# The counted batch is linear in each whole native-table budget

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `prop:time`, paper/paper.tex: the actual
count decoder and its explicit tape return have polynomial scalar work. -/
theorem countHeaderReadCost_le (T : ℕ) : countHeaderReadCost T≤2000*(T+1)^2 := by
  have hb := natBitLength_le_self_succ T
  have hp := two_pow_natBitLength_le T
  have hm := Nat.mul_le_mul (by omega : natBitLength T+2≤T+3)
    (by omega : 40*2^natBitLength T+40≤80*T+120)
  unfold countHeaderReadCost
  nlinarith

/-- `prop:time`, paper/paper.tex: every indexed
whole-test body pays its literal input, native call, and reusable-bank
cleanup, with polynomial dependence only on the finite test count. -/
theorem indexedOccurrenceCost_le {I : Type} {input : I→List Bool}
    (F : StagePrint.PoolFamily I input) (budget : I→ℕ) (B : ℕ)
    (hb : ∀j,budget (F.request j)≤B) (j : Fin F.count) :
    StagePrint.poolOccurrenceCost j.val F.source.length (input (F.request j)).length
      (budget (F.request j))≤20000*(F.count+1)^2+1000*(F.source.length+B+1) := by
  have hj := j.isLt
  have hbits := StagePrint.pool_index_bits j.val
  have hsquare := Nat.pow_le_pow_left (by omega : j.val+1≤F.count+1) 2
  have hbudget := hb j
  have hi : (input (F.request j)).length=2*natBitLength j.val+1+F.source.length := by
    rw [F.indexed]
    simp [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]
  unfold StagePrint.poolOccurrenceCost StagePrint.writeIndexedCost StagePrint.callAppendCost
  rw [hi]
  nlinarith

/-- `prop:time`, paper/paper.tex: the complete
step-budget sum retains a single factor of the true whole-table budget. -/
theorem batchStepBudget_le {I : Type} {input : I→List Bool}
    (F : StagePrint.PoolFamily I input) (budget : I→ℕ) (B : ℕ)
    (hb : ∀j,budget (F.request j)≤B) :
    F.stepBudget budget≤F.count*(20000*(F.count+1)^2+1000*(F.source.length+B+1)) := by
  let A := 20000*(F.count+1)^2+1000*(F.source.length+B+1)
  have sumBound (xs : List ℕ) (h : ∀x∈xs,x≤A) : xs.sum≤xs.length*A := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := h x (by simp)
      have hh := ih (fun y hy => h y (by simp [hy]))
      simp only [List.sum_cons,List.length_cons]
      nlinarith
  unfold StagePrint.PoolFamily.stepBudget
  refine (sumBound _ ?_).trans_eq ?_
  · intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact indexedOccurrenceCost_le F budget B hb j
  · simp [A]

/-- `prop:time`, paper/paper.tex: every cached
native byte was physically written by its actual table program, so the
complete cache volume is bounded by the sum of real native budgets. -/
theorem batchCacheBytes_le {I : Type} {input payload : I→List Bool} {budget : I→ℕ}
    (provider : WordFunction I input (fun r => frame (payload r)) budget)
    (F : StagePrint.PoolFamily I input) (B : ℕ) (hb : ∀j,budget (F.request j)≤B) :
    (StagePrint.poolPrefix (F.caches payload) F.count).length≤F.count*(B+1) := by
  have hp : ∀n,n≤F.count→(StagePrint.poolPrefix (F.caches payload) n).length≤n*(B+1) := by
    intro n
    induction n with
    | zero => intro _;simp [StagePrint.poolPrefix]
    | succ n ih =>
      intro hn
      have hlt : n<F.count := by omega
      let j : Fin F.count := ⟨n,hlt⟩
      have hout := Control.output_length_le provider (F.request j)
      have hc : F.caches payload n=payload (F.request j) := by simp [StagePrint.PoolFamily.caches,hlt,j]
      rw [StagePrint.poolPrefix_succ,List.length_append,hc]
      have hh := ih (by omega)
      have hB := hb j
      nlinarith
  exact hp F.count le_rfl

/-- `prop:time`, paper/paper.tex: scalar
indexing and count work are polynomial in the test count, while the
whole native table budget occurs only linearly. -/
def batchWorkBound (T sourceLength countBudget nativeBudget : ℕ) : ℕ :=
  2*(400*(sourceLength+countBudget+1)+2000*(T+1)^2+100+
    (T*(T*(20000*(T+1)^2+1000*(sourceLength+nativeBudget+1))+10)+1)+
    (1000*(sourceLength+T*(nativeBudget+1)+1)+10000*(T+1)^2)+2)+2

/-- `prop:time`, paper/paper.tex: the actual
compiled batch inherits a linear whole-native-budget bound, including
all cached bytes and the paid final parallel head return. -/
theorem batchedMachineBudget_le {I : Type} {input payload : I→List Bool} {budget : I→ℕ}
    (provider : WordFunction I input (fun r => frame (payload r)) budget)
    (F : StagePrint.PoolFamily I input) (countBudget B : ℕ) (hb : ∀j,budget (F.request j)≤B) :
    batchedMachineBudget F payload budget countBudget≤batchWorkBound F.count F.source.length countBudget B := by
  have hs := batchStepBudget_le F budget B hb
  have hc := batchCacheBytes_le provider F B hb
  have hh := countHeaderReadCost_le F.count
  have hm := Nat.mul_le_mul_left F.count (Nat.add_le_add_right hs 10)
  unfold batchedMachineBudget batchedTablesCost poolCountCost StagePrint.PoolFamily.loopBudget
    flattenPoolCost batchWorkBound
  omega

end NearQuarticWires.StageCertificateControl
