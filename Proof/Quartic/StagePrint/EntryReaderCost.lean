import Proof.Quartic.StagePrint.EntryColdMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: complete
physical acquisition and output use only a linear number of finite
source bits and the original metadata's arithmetic magnitude. -/
theorem coldSteps_linear {modular : Bool} (r : Request modular) :
    coldSteps r≤10000*(r.word.length+r.sizingMagnitude+1) := by
  have hl:=r.field_lengths_le
  have hbits (v : ℕ) : natBitLength v≤v+1 := by
    unfold natBitLength
    have h:=Nat.log_le_self 2 v
    omega
  have hwidth : r.termRequest.stackWidth≤r.sizingMagnitude := by
    rw [r.stackWidth_actual]
    unfold NativeWidth.packedBits Request.sizingMagnitude
    dsimp only
    omega
  have hW:=hbits r.termRequest.stackWidth
  have hn:=hbits r.header.call.n
  have hsize : Nat.size r.header.call.n≤r.header.call.n :=
    Nat.size_le.mpr (Nat.lt_two_pow_self (n:=r.header.call.n))
  have hmag : r.header.call.n+natBitLength r.scale+natBitLength r.walkCode.val+
      natBitLength r.degree≤r.sizingMagnitude := by
    unfold Request.sizingMagnitude
    dsimp only
    omega
  unfold coldSteps readerSteps prefixSteps writerSteps
  omega

/-- `prop:time`, paper/paper.tex: the actual
ordinary formatter clock is linear in the real finite Terms source,
with a fixed polynomial original-arity multiplier. -/
theorem allocatedBudget_linear {C E : ℕ} {modular : Bool}
    (allocation : Allocation C E modular) :
    ∃ K e : ℕ,∀ r : BoundedRequest C E modular,
      allocatedBudget allocation r≤K*(r.word.length+1)*(r.header.call.n+1)^e := by
  obtain ⟨K,e,hbudget⟩:=allocation.linear_budget
  refine ⟨K*10002*(C+1),E+e,?_⟩
  intro r
  have hs:=coldSteps_linear r.toRequest
  have hm:=r.size_bound
  have hp : 1≤(r.header.call.n+1)^E:=Nat.one_le_pow _ _ (by omega)
  have hsum : r.word.length+r.toRequest.sizingMagnitude+1≤
      (C+1)*(r.word.length+1)*(r.header.call.n+1)^E := by
    have h1 : r.word.length+1≤(r.word.length+1)*(r.header.call.n+1)^E :=
      Nat.le_mul_of_pos_right _ hp
    have h2 : C*(r.header.call.n+1)^E≤C*(r.word.length+1)*(r.header.call.n+1)^E :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right C (by omega))
    calc
      _ ≤ r.word.length+C*(r.header.call.n+1)^E+1 := by omega
      _ ≤ (r.word.length+1)*(r.header.call.n+1)^E+
          C*(r.word.length+1)*(r.header.call.n+1)^E := by omega
      _ = _ := by ring
  have hsteps : r.word.length+coldSteps r.toRequest+1≤
      10002*(C+1)*(r.word.length+1)*(r.header.call.n+1)^E := by
    have hlen : r.word.length≤r.word.length+r.toRequest.sizingMagnitude+1 := by omega
    have hsum' := Nat.mul_le_mul_left 10002 hsum
    change coldSteps r.toRequest≤10000*(r.word.length+r.toRequest.sizingMagnitude+1) at hs
    nlinarith only [hs,hlen,hsum']
  unfold allocatedBudget
  calc
    _ ≤ K*(r.word.length+coldSteps r.toRequest+1)*(r.header.call.n+1)^e :=
      hbudget r (coldSteps r.toRequest)
    _ ≤ K*(10002*(C+1)*(r.word.length+1)*(r.header.call.n+1)^E)*(r.header.call.n+1)^e :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hsteps)
    _ = K*10002*(C+1)*(r.word.length+1)*(r.header.call.n+1)^(E+e) := by
      rw [pow_add]
      ring

end NearQuarticWires.StagePrint.EntryFormat
