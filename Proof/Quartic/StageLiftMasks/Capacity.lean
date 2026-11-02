import Proof.Quartic.StageLiftMasks.Bounds

/-!
# Space for the original tuple enumeration

`lem:maskpoly` and `prop:time`, paper/paper.tex: the selected quadratic word width
contains every actual tuple counter and source address, even when
the number of enumerated tuples is exponential in the mask degree.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open NearCubicWires NearCubicGates.Close.Cells StageLift

structure MaskCapacity {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) (W : ℕ) : Prop where
  minWidth : 5≤W
  prepared : (preparedWordOf r).length<2^W
  patterns : 2*r.child.selected.1.N≤2^W
  atomIndex : 17*(Builder.allGates r.child.call).length<2^W
  address : r.child.selected.1.k+(Builder.allGates r.child.call).length≤2^W
  tuples : 2*(Builder.allGates r.child.call).length^r.child.selected.1.Xmax≤2^W
  newtonArithmetic : 2*r.child.selected.1.Xmax+2≤W
  limit : r.child.selected.1.Xmax+1<2^W
  atomWord : 2*(sourceEnvelope r+1)+2<2^W
  newtonWord : 4*(sourceEnvelope r+1)+2<2^W
  patternWord : sourceEnvelope r+1+2<2^W

theorem source_mask_capacity {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) (W : ℕ)
    (hW : 100*(sourceEnvelope r+1)^2≤W) : MaskCapacity r W := by
  let E:=sourceEnvelope r
  have he:=(sourceEnvelope_bounds r).positive
  have hG:=(sourceEnvelope_bounds r).occurrences
  have hk:=(sourceEnvelope_bounds r).partition
  have hx:=source_Xmax_le r
  have hp:=prepared_length_le r
  have hsq : E+1≤(E+1)^2 := Nat.le_self_pow (by decide) _
  have hlin : 100*(E+1)≤W := by dsimp [E] at *; nlinarith only [hW,hsq]
  have hpow : W<2^W := Nat.lt_two_pow_self
  have htuple : 2*(Builder.allGates r.child.call).length^r.child.selected.1.Xmax≤2^W := by
    have hh:=StageLiftTokens.source_modulus_bound E _ _ hG hx
    have hexp : E*E+1≤W := by dsimp [E] at *; nlinarith only [hW]
    have hbound:=Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hexp
    rw [pow_succ] at hbound
    omega
  have hn : 2*r.child.selected.1.N≤2^W := by
    have hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
    rw [hs.N_eq]
    have hd:=Nat.div_le_self r.child.selected.1.k 2
    have hbound:=Nat.pow_le_pow_right (by decide : 1≤(2:ℕ))
      (show r.child.selected.1.k/2+1≤W by dsimp [E] at hlin; omega)
    rw [pow_succ] at hbound
    omega
  dsimp [E] at hlin
  exact ⟨by omega,by omega,hn,by omega,by omega,htuple,by omega,
    by omega,by omega,by omega,by omega⟩

end NearQuarticWires.StageLiftMasks
