import Proof.Quartic.StageTupleSetup.WidthProgram

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetup

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CellsPack (Gof)

theorem widthSourceClock_bound (W : ℕ) : widthSourceClock W≤1000*(W+1) := by
  have h0:=StageResize.bitLength_le W
  have h1:=StageResize.bitLength_le (W+1)
  unfold widthSourceClock widthRawClock widthBodyClock
  omega

theorem widthSetup_upper (W : ℕ) :
    widthSizes.W (leadOnes (natWord W))≤200*(W+1) := by
  have hl : leadOnes (natWord W)=natBitLength W := by
    simpa only [List.append_nil] using
      NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord W []
  simp only [widthSizes,Sz.W,one_mul,hl,natBitLength,pow_succ]
  have hh:=Nat.pow_log_le_add_one 2 W
  omega

theorem widthWorkspace_scalar (W L V T : ℕ) (hW : W≤200*V) (hL : L≤V) (hV : 1≤V) :
    W+L+100+1+T+1≤(T+1000)*V := by nlinarith

theorem widthCompilation_scalar (A V : ℕ) (hA : 1≤A) :
    10^6*((1001*V)*(A*V)^2)+30*V≤10^13*A^2*V^3 := by
  have hv : V≤V^3 := Nat.le_self_pow (by decide) V
  have ha : 1≤A^2 := Nat.one_le_pow _ _ hA
  have hs : 30*V≤30*A^2*V^3 := by
    have hh:=hv.trans (Nat.le_mul_of_pos_left _ ha)
    nlinarith only [hh]
  have he : 10^6*((1001*V)*(A*V)^2)=1001000000*A^2*V^3 := by ring
  rw [he]
  nlinarith only [hs]

noncomputable def widthCostConstant : ℕ :=10^13*(TSK StageResize.resizeCallee+1000)^2

/-- `prop:time`, paper/paper.tex: the actual
width-successor cold machine has a polynomial budget in its separate
width value, with no complete-source/Terms length in its arithmetic. -/
theorem widthBudget_polynomial (W : ℕ) : widthBudget W≤widthCostConstant*(W+1)^3 := by
  let V:=W+1
  let A:=TSK StageResize.resizeCallee+1000
  have hV : 1≤V := by dsimp [V];omega
  have hA : 1≤A := by dsimp [A];omega
  have hL : leadOnes (natWord W)≤V := by
    have hl : leadOnes (natWord W)=natBitLength W := by
      simpa only [List.append_nil] using
        NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord W []
    rw [hl]
    exact StageResize.bitLength_le W
  have hG : Gof StageResize.resizeCallee widthSizes (leadOnes (natWord W))≤A*V := by
    simp only [Gof,Sz.Lk,Sz.Bk,widthSizes,Nat.zero_mul,pow_zero,mul_zero,add_zero]
    change widthSizes.W (leadOnes (natWord W))+leadOnes (natWord W)+100+1+
      TSK StageResize.resizeCallee+1≤A*V
    exact widthWorkspace_scalar _ _ _ _ (widthSetup_upper W) hL hV
  have hN : widthSourceClock W+1≤1001*V := by
    have hh:=widthSourceClock_bound W
    change widthSourceClock W≤1000*V at hh
    omega
  have hI : (natWord W).length≤3*V := by
    rw [NearCubicGates.Close.Cells.natWord_length]
    have hh:=StageResize.bitLength_le W
    dsimp [V]
    omega
  have hh:=NearCubicGates.Close.CellsPack.lang_le2 StageResize.resizeCallee widthSizes
    (natWord W) (widthSourceClock W)
  calc
    widthBudget W≤10^6*((widthSourceClock W+1)*
      Gof StageResize.resizeCallee widthSizes (leadOnes (natWord W))^2)+10*(natWord W).length:=hh
    _≤10^6*((1001*V)*(A*V)^2)+30*V:=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul hN (Nat.pow_le_pow_left hG 2)))
        (by have hi:=Nat.mul_le_mul_left 10 hI;nlinarith only [hi])
    _≤10^13*A^2*V^3:=widthCompilation_scalar A V hA
    _=widthCostConstant*(W+1)^3:=rfl

end NearQuarticWires.StageTupleSetup
