import Proof.Quartic.StagePrint.EntryAllocationTarget
import Proof.Gates.CounterMachine.PrefixFinal

set_option autoImplicit false

namespace NearQuarticWires.StageEntryAllocation

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.CounterMachine.PrefixProg
open StagePrint.EntryFormat

/-- `lem:print`, paper/paper.tex: the one fixed
allocator uses the original arity's leading binary-length field and
reserves no callee input or output space. -/
def sizes (C E : ℕ) : Sz := ⟨10*(C+1),E+2,0,0,0,0⟩

/-- `lem:print`, paper/paper.tex: the actual
unchanged formatter input starts with the original arity codec in both modes. -/
theorem original_header {C E : ℕ} {modular : Bool} (r : BoundedRequest C E modular) :
    leadOnes r.word=natBitLength r.header.call.n := by
  change leadOnes r.toRequest.word=_
  unfold Request.word
  simp only [List.append_assoc]
  exact leadOnes_natWord _ _

/-- `lem:print` and `prop:time`, paper/paper.tex: all required arithmetic and logarithmic finite-stream
heights fit the real initialized word width, with constant spare space. -/
theorem required_width (C E : ℕ) (modular : Bool) (r : BoundedRequest C E modular) :
    r.toRequest.sizingMagnitude+10≤(sizes C E).W (leadOnes r.word) := by
  have hn : r.header.call.n+1≤2^natBitLength r.header.call.n := lt_natBitLength _
  have hp : (r.header.call.n+1)^E≤2^((E+2)*natBitLength r.header.call.n) := by
    calc
      _≤(2^natBitLength r.header.call.n)^E := Nat.pow_le_pow_left hn _
      _=2^(E*natBitLength r.header.call.n) := by rw [←pow_mul,Nat.mul_comm]
      _≤_ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  have hfit:=Nat.mul_le_mul_right (10*(C+1)) hp
  have hone : 1≤(r.header.call.n+1)^E := Nat.one_le_pow _ _ (by omega)
  have hm:=r.size_bound
  rw [original_header]
  change r.toRequest.sizingMagnitude+10≤2^((E+2)*natBitLength r.header.call.n)*(10*(C+1))
  nlinarith only [hfit,hone,hm]

/-- `prop:time`, paper/paper.tex: this actual
header-derived width is a fixed polynomial in original arity, uniformly
over every actual Terms payload and source execution length. -/
theorem width_polynomial (C E n : ℕ) :
    (sizes C E).W (natBitLength n)≤(10*(C+1)*2^(E+2))*(n+1)^(E+2) := by
  have hp:=Nat.pow_le_pow_left (pow_nbl_le n) (E+2)
  unfold Sz.W sizes
  dsimp only
  calc
    _=(2^natBitLength n)^(E+2)*(10*(C+1)) := by rw [←pow_mul,Nat.mul_comm (E+2)]
    _≤(2*(n+1))^(E+2)*(10*(C+1)) := Nat.mul_le_mul_right _ hp
    _=_ := by rw [mul_pow];ring

end NearQuarticWires.StageEntryAllocation
