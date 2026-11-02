import Proof.Quartic.StageCert.StreamLengths
import Proof.Gates.CellsPack.Lang

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CellsPack (Gof)
open NearCubicWires NearCubicWires.RepairRepresentation

/-- `prop:time`, paper/paper.tex: the table header sets the
arithmetic width to at most a fixed multiple of its declared scalar height. -/
theorem table_setup_width_le (r : CertTableRequest) :
    recordSizes.W (leadOnes (certTableWord r)) ≤ 32*(tableWidth r+1) := by
  have he : leadOnes (certTableWord r) = natBitLength (tableWidth r) := by
    unfold certTableWord
    simpa only [List.append_assoc] using
      NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord (tableWidth r)
        (natWord r.payload.length ++ r.payload ++ natWord (if r.doAppend then 1 else 0) ++
          NearCubicGates.Close.Interfaces.listWord
            (NearCubicGates.Close.Interfaces.listWord momentRecordWord) r.columns)
  simp only [Sz.W,recordSizes,he,Nat.one_mul,natBitLength,pow_succ]
  have h := Nat.pow_log_le_add_one 2 (tableWidth r)
  omega

/-- `prop:time`, paper/paper.tex: the compiled finisher has
linear record-count and cubic scalar-height cost, including every stream
setup, arithmetic operation and final rewind. -/
theorem finishLanguageBudget_le (K : Callee) (r : CertTableRequest) :
    langBudget K recordSizes VV MM (certTableWord r)
      (10^7*(r.payload.length+streamWork r.columns+tableWidth r+1)*
        (recordSizes.W (leadOnes (certTableWord r))+1)) ≤
      10^16*(TSK K+100)^2*(r.payload.length+streamWork r.columns+tableWidth r+1)*
        (tableWidth r+1)^3 := by
  let W := tableWidth r+1
  let P := r.payload.length+streamWork r.columns+tableWidth r+1
  let A := TSK K+100
  let N := 10^7*P*(recordSizes.W (leadOnes (certTableWord r))+1)
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hP : 1 ≤ P := by dsimp [P]; omega
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hL : leadOnes (certTableWord r) ≤ W := by
    have he : leadOnes (certTableWord r) = natBitLength (tableWidth r) := by
      unfold certTableWord
      simpa only [List.append_assoc] using
        NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord (tableWidth r)
          (natWord r.payload.length ++ r.payload ++ natWord (if r.doAppend then 1 else 0) ++
            NearCubicGates.Close.Interfaces.listWord
              (NearCubicGates.Close.Interfaces.listWord momentRecordWord) r.columns)
    rw [he]
    exact Nat.add_le_add_right (Nat.log_le_self 2 _) 1
  have hG : Gof K recordSizes (leadOnes (certTableWord r)) ≤ A*W := by
    have hw := table_setup_width_le r
    simp only [Gof,Sz.Lk,Sz.Bk,recordSizes,Nat.zero_mul,pow_zero,mul_zero,add_zero]
    change recordSizes.W (leadOnes (certTableWord r))+leadOnes (certTableWord r)+
      16+0+0+1+0+0+TSK K+1 ≤ A*W
    dsimp [A,W] at *
    nlinarith
  have hN : N+1 ≤ 330000001*P*W := by
    have hw := table_setup_width_le r
    have hpos : 1 ≤ P*W := Nat.mul_pos hP hW
    dsimp [N,W] at *
    nlinarith
  have hsmall : 200*P*W ≤ 200*A^2*P*W^3 := by
    have hpow : W ≤ W^3 := Nat.le_self_pow (by decide : (3:ℕ)≠0) W
    have ha : 1 ≤ A^2 := Nat.one_le_pow _ _ hA
    have hp : P*W ≤ A^2*P*W^3 := by
      calc
        P*W ≤ P*W^3 := Nat.mul_le_mul_left _ hpow
        _ ≤ A^2*(P*W^3) := Nat.le_mul_of_pos_left _ ha
        _ = _ := by ring
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 200 hp
  have h := NearCubicGates.Close.CellsPack.lang_le2 K recordSizes (certTableWord r) N
  calc
    _ ≤ 10^6*((N+1)*Gof K recordSizes (leadOnes (certTableWord r))^2)+
        10*(certTableWord r).length := h
    _ ≤ 10^6*((330000001*P*W)*(A*W)^2)+200*P*W := by
      have hp := Nat.mul_le_mul hN (Nat.pow_le_pow_left hG 2)
      apply Nat.add_le_add (Nat.mul_le_mul_left _ hp)
      have hi := Nat.mul_le_mul_left 10 (certTableWord_length_le r)
      calc
        10*(certTableWord r).length ≤
          10*(20*(r.payload.length+streamWork r.columns+tableWidth r+1)*(tableWidth r+1)) := hi
        _ = 200*P*W := by dsimp [P,W]; ring
    _ ≤ 10^16*A^2*P*W^3 := by
      have he : 10^6*((330000001*P*W)*(A*W)^2) = 330000001000000*A^2*P*W^3 := by ring
      rw [he]
      nlinarith only [hsmall]
    _ = _ := rfl

/-- `prop:time`, paper/paper.tex: the actual physical
certificate-finisher budget is linear in the record count and polynomial in
its scalar field heights. -/
theorem finishBudget_polynomial : ∃ K : ℕ, ∀ r : CertTableRequest,
    finishBudget r ≤ K*(r.payload.length+streamWork r.columns+1)*(tableWidth r+1)^4 := by
  refine ⟨10^16*(TSK recordCallee+100)^2,?_⟩
  intro r
  have h := finishLanguageBudget_le recordCallee r
  change finishBudget r ≤ _ at h
  have hp : r.payload.length+streamWork r.columns+tableWidth r+1 ≤
      (r.payload.length+streamWork r.columns+1)*(tableWidth r+1) := by nlinarith
  calc
    finishBudget r ≤ _ := h
    _ ≤ 10^16*(TSK recordCallee+100)^2*
        ((r.payload.length+streamWork r.columns+1)*(tableWidth r+1))*(tableWidth r+1)^3 := by gcongr
    _ = _ := by ring

end NearQuarticWires.StageCert
