import Proof.Quartic.StageCertNative.ExpandFrame
import Proof.Quartic.StageGreedyEntryBounds.Codec
import Proof.Gates.CounterMachine.PrefixFinal

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Expand.PolyTab NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- `lem:print` and `prop:time`, paper/paper.tex: copying one actual signed monomial has a polynomial
price in its original atom count and coefficient-bit bound. -/
theorem cpMonoCost_bits {V bits : ℕ} (t : Finset (Fin V)×ℤ)
    (hc : t.2.natAbs<2^bits) :
    cpMonoCost t≤10000*(V+bits+10)^3 := by
  let S:=V+bits+10
  let xs:=(t.1.sort (·≤·)).map Fin.val
  have hS : 10≤S := by dsimp only [S];omega
  have hm : xs.length≤V := by
    simp only [xs,List.length_map,Finset.length_sort]
    exact (Finset.card_le_univ t.1).trans_eq (by simp)
  have hmS : xs.length≤S := by omega
  have hnbl : natBitLength xs.length≤S :=
    (NearCubicGates.Close.Dispatch.natBitLength_le_succ _).trans (by omega)
  have hpow : 2^natBitLength xs.length≤4*S :=
    (NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le _).trans (by omega)
  have hbytes : ∀x∈xs,(natWord x).length≤2*S+3 := by
    intro x hx
    obtain ⟨i,_hi,rfl⟩:=List.mem_map.mp hx
    have hh:=NearCubicGates.Close.Dispatch.natBitLength_le_succ i.val
    have hi:=i.isLt
    rw [NearCubicGates.Close.CounterAsm.natWord_len]
    omega
  have hsum : ((xs.map fun x=>60*(natWord x).length+60).map fun c=>c+4).sum≤
      S*(60*(2*S+3)+64) := by
    have hh:=List.sum_le_card_nsmul
      ((xs.map fun x=>60*(natWord x).length+60).map fun c=>c+4)
      (60*(2*S+3)+64) (by
        intro v hv
        obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hv
        obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hc
        have hh:=hbytes x hx
        omega)
    simp only [List.length_map,smul_eq_mul] at hh
    exact hh.trans (Nat.mul_le_mul_right _ hmS)
  have hsign : (natWord (if t.2<0 then 1 else 0)).length=3 := by
    split_ifs <;> rfl
  have hcoeff : (NearCubicGates.Close.Interfaces.intWord t.2).length≤2*S+6 := by
    have hh:=NearCubicGates.Close.Expand.Layout.natWord_len_le _ _ hc
    simp only [NearCubicGates.Close.Interfaces.intWord,List.length_append,hsign]
    omega
  have hread : (natBitLength xs.length+2)*(40*2^natBitLength xs.length+40)≤
      (S+2)*(160*S+40) := Nat.mul_le_mul (by omega) (by omega)
  have hbook : (natBitLength xs.length+10)*(100*xs.length+200)≤
      (S+10)*(100*S+200) := Nat.mul_le_mul (by omega) (by omega)
  change NearCubicGates.Close.Codec.copyListCost xs.length
    (xs.map fun x=>60*(natWord x).length+60)+1+
      (60*(NearCubicGates.Close.Interfaces.intWord t.2).length+121)≤10000*S^3
  unfold NearCubicGates.Close.Codec.copyListCost
  have h23 : S^2≤S^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have h13 : S≤S^3 := Nat.le_self_pow (by decide) _
  have h03 : 1≤S^3 := Nat.one_le_pow _ _ (by omega)
  nlinarith only [hread,hbook,hsum,hcoeff,hS,h23,h13,h03]

/-- `lem:print` and `prop:time`, paper/paper.tex: distinct actual supports bound the count-header
height, so the complete physical Terms framer has linear record-byte
cost with a fixed polynomial atom/coefficient-bit multiplier. -/
theorem cpTermsCost_bits {V bits : ℕ} (P : Terms V)
    (hn : (Terms.keys P).Nodup) (hc : ∀t∈P,t.2.natAbs<2^bits) :
    cpTermsCost P≤100000*(V+bits+10)^4*(P.length+(termsWord P).length+1) := by
  let S:=V+bits+10
  have hS : 10≤S := by dsimp only [S];omega
  have hm:=StageGreedyEntryBounds.terms_count V P hn
  have hnbl : natBitLength P.length≤V+1 := by
    have hh:=Nat.add_le_add_right (Nat.log_mono_right (b:=2) hm) 1
    have he : natBitLength (2^V)=V+1 := by
      unfold natBitLength
      rw [Nat.log_pow (by decide : 1<(2:ℕ))]
    change natBitLength P.length≤natBitLength (2^V) at hh
    exact hh.trans_eq he
  have hp:=NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le P.length
  have hsum : ((P.map cpMonoCost).map fun c=>c+4).sum≤P.length*(10000*S^3+4) := by
    have hh:=List.sum_le_card_nsmul ((P.map cpMonoCost).map fun c=>c+4)
      (10000*S^3+4) (by
        intro v hv
        obtain ⟨c,hc',rfl⟩:=List.mem_map.mp hv
        obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hc'
        have hh:=cpMonoCost_bits t (hc t ht)
        exact Nat.add_le_add_right hh 4)
    simpa only [List.length_map,smul_eq_mul] using hh
  have hread : (natBitLength P.length+2)*(40*2^natBitLength P.length+40)≤
      (S+2)*(80*(P.length+1)+40) := Nat.mul_le_mul (by omega) (by omega)
  have hbook : (natBitLength P.length+10)*(100*P.length+200)≤
      (S+10)*(100*P.length+200) := Nat.mul_le_mul (by omega) (by omega)
  have h34 : S^3≤S^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h14 : S≤S^4 := Nat.le_self_pow (by decide) _
  have h04 : 1≤S^4 := Nat.one_le_pow _ _ (by omega)
  have hm14:=Nat.mul_le_mul_left P.length h14
  have hm34:=Nat.mul_le_mul_left P.length h34
  have hm04:=Nat.mul_le_mul_left P.length h04
  have hw04:=Nat.mul_le_mul_left (termsWord P).length h04
  unfold cpTermsCost NearCubicGates.Close.Codec.copyListCost
  change _≤100000*S^4*(P.length+(termsWord P).length+1)
  nlinarith only [hread,hbook,hsum,hS,h34,h14,h04,hm14,hm34,hm04,hw04]

end NearQuarticWires.StageCertNative
