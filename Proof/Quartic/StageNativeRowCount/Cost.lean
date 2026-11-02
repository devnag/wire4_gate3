import Proof.Quartic.StageNativeRowCount.WordFunction

set_option autoImplicit false

namespace NearQuarticWires.StageNativeRowCount

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CellsPack (Gof)

/-- `prop:time`, paper/paper.tex: the original
arity and actual finite encoded bytes, not translation value, pay the run. -/
def Request.costScale (r : Request) : ℕ := r.header.call.n+r.word.length+1

theorem Request.sourceClock_bound (r : Request) : r.sourceClock≤20000*r.costScale^2 := by
  let n:=r.header.call.n
  let V:=r.costScale
  have hv : n+1≤V := by unfold V Request.costScale;omega
  have h1 : 1≤V := by omega
  have hT : (n+1)^2≤V^2 := Nat.pow_le_pow_left hv 2
  have hV : V≤V^2 := Nat.le_self_pow (by decide) V
  have hp : r.payload.length≤V := by
    change r.payload.length≤n+(frame r.payload).length+1
    rw [frame_length]
    omega
  have hb : ∀v∈r.firstFive,natBitLength v≤16*V^2+1 := by
    intro v hvv
    have hh:=r.firstFive_bound v hvv
    have hbits:=bitLength_le v
    change v≤16*(n+1)^2 at hh
    omega
  have hn:=hb n (by simp [Request.firstFive,n])
  have hl:=hb r.sourceWidth (by simp [Request.firstFive])
  have ho:=hb r.nativeWidth (by simp [Request.firstFive])
  have hr:=hb r.header.parameters.r (by simp [Request.firstFive])
  have hbb:=hb r.header.parameters.b (by simp [Request.firstFive])
  have hc : natBitLength r.rowFieldCount≤4*n+4 :=
    (bitLength_le r.rowFieldCount).trans (by have hh:=r.count_bound;change r.rowFieldCount≤4*n+3 at hh;omega)
  unfold Request.sourceClock Request.unframedClock Request.bodyClock parseHeaderCost
  change 3*(9*r.payload.length+
    (30*(natBitLength n+natBitLength r.header.parameters.r+natBitLength r.header.parameters.b)+
    20*(natBitLength r.sourceWidth+natBitLength r.nativeWidth)+200)+
    40*natBitLength r.rowFieldCount+100+6)+2≤20000*V^2
  nlinarith

theorem scalar_workspace_bound (W L V T : ℕ)
    (hW : W≤80000*V^2) (hL : L≤3*V^2) (hV : 1≤V) :
    W+L+10000+1+T+1≤(T+100000)*V^2 := by
  have h2 : 1≤V^2 := Nat.one_le_pow _ _ hV
  nlinarith

theorem Request.workspace_bound (r : Request) :
    Gof rowCountCallee rowCountSizes (leadOnes r.word)≤
      (TSK rowCountCallee+100000)*r.costScale^2 := by
  let V:=r.costScale
  have hv : r.header.call.n+1≤V := by dsimp [V,Request.costScale];omega
  have h1 : 1≤V := by omega
  have hW : rowCountSizes.W (leadOnes r.word)≤80000*V^2 :=
    r.setup_upper.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hv 2))
  have hL : leadOnes r.word≤3*V^2 := by
    rw [r.leading]
    have hb:=bitLength_le r.header.call.n
    have hV : V≤V^2 := Nat.le_self_pow (by decide) V
    nlinarith only [hb,hv,hV]
  simp only [Gof,Sz.Lk,Sz.Bk,rowCountSizes,Nat.zero_mul,pow_zero,mul_zero,add_zero]
  change rowCountSizes.W (leadOnes r.word)+leadOnes r.word+10000+1+TSK rowCountCallee+1≤_
  exact scalar_workspace_bound (rowCountSizes.W (leadOnes r.word))
    (leadOnes r.word) V (TSK rowCountCallee) hW hL h1

theorem scalar_compilation_bound (A V : ℕ) (hA : 1≤A) :
    10^6*((20001*V^2)*(A*V^2)^2)+10*V≤10^12*A^2*V^6 := by
  have hv : V≤V^6 := Nat.le_self_pow (by decide) V
  have ha : 1≤A^2 := Nat.one_le_pow _ _ hA
  have hh : 10*V≤10*A^2*V^6 := by
    have hp:=hv.trans (Nat.le_mul_of_pos_left _ ha)
    nlinarith only [hp]
  have he : 10^6*((20001*V^2)*(A*V^2)^2)=20001000000*A^2*V^6 := by ring
  rw [he]
  nlinarith only [hh]

noncomputable def costConstant : ℕ := 10^12*(TSK rowCountCallee+100000)^2

/-- `prop:time`, paper/paper.tex: the actual cold
native field-count producer has a fixed polynomial cost in the original
arity plus finite encoded input bytes, independently of translation value. -/
theorem Request.budget_polynomial (r : Request) :
    r.budget≤costConstant*(r.header.call.n+r.word.length+1)^6 := by
  let V:=r.costScale
  let A:=TSK rowCountCallee+100000
  have hV : 1≤V := by dsimp [V,Request.costScale];omega
  have hA : 1≤A := by dsimp [A];omega
  have hN : r.sourceClock+1≤20001*V^2 := by
    have hh:=r.sourceClock_bound
    change r.sourceClock≤20000*V^2 at hh
    have hp : 1≤V^2 := Nat.one_le_pow _ _ hV
    omega
  have hi : r.word.length≤V := by dsimp [V,Request.costScale];omega
  have hG : Gof rowCountCallee rowCountSizes (leadOnes r.word)≤A*V^2 := r.workspace_bound
  have hh:=NearCubicGates.Close.CellsPack.lang_le2 rowCountCallee rowCountSizes r.word r.sourceClock
  calc
    r.budget≤10^6*((r.sourceClock+1)*Gof rowCountCallee rowCountSizes (leadOnes r.word)^2)+10*r.word.length:=hh
    _≤10^6*((20001*V^2)*(A*V^2)^2)+10*V:=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul hN (Nat.pow_le_pow_left hG 2)))
        (Nat.mul_le_mul_left _ hi)
    _≤10^12*A^2*V^6:=scalar_compilation_bound A V hA
    _=costConstant*(r.header.call.n+r.word.length+1)^6:=rfl

end NearQuarticWires.StageNativeRowCount
