import Proof.Quartic.StagePrint.EntrySizing
import Proof.Gates.Expand.Cost2

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntryBounds

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Expand.Layout

/-- `lem:print`, paper/paper.tex: a canonical
support and bounded signed coefficient have a polynomial byte height. -/
def recordHeight (V bits : ℕ) : ℕ := 2*V+3+V*(2*V+3)+5+(2*bits+3)

/-- `lem:print`, paper/paper.tex: this bound
uses the actual finite support and coefficient codec, without Formula weight. -/
theorem monoWord_length (V bits : ℕ) (t : Finset (Fin V)×ℤ)
    (hc : t.2.natAbs<2^bits) : (monoWord t).length≤recordHeight V bits := by
  have hcard : t.1.card≤V := by simpa only [Fintype.card_fin] using Finset.card_le_univ t.1
  have hhead:=natWord_len_le t.1.card V (lt_of_le_of_lt hcard Nat.lt_two_pow_self)
  have hcoeff:=natWord_len_le t.2.natAbs bits hc
  have hsign:=natWord_len_le (if t.2<0 then 1 else 0) 1 (by split_ifs <;> norm_num)
  have hvars : ((t.1.sort (·≤·)).map fun v : Fin V=>(natWord v.val).length).sum≤V*(2*V+3) := by
    have hs:=List.sum_le_card_nsmul ((t.1.sort (·≤·)).map fun v : Fin V=>(natWord v.val).length)
      (2*V+3) (by
        intro x hx
        obtain ⟨v,_,rfl⟩:=List.mem_map.mp hx
        exact natWord_len_le _ _ (lt_trans v.isLt Nat.lt_two_pow_self))
    simp only [List.length_map,Finset.length_sort,smul_eq_mul] at hs
    exact hs.trans (Nat.mul_le_mul_right _ hcard)
  simp only [monoWord,listWord,NearCubicGates.Close.Interfaces.intWord,List.length_append,List.length_map,
    Finset.length_sort,List.length_flatMap,List.map_map,Function.comp_def]
  unfold recordHeight
  omega

/-- `lem:print`, paper/paper.tex: distinct actual
Terms keys are subsets of the original atom set, hence their count is
at most its full powerset, regardless of their coefficient values. -/
theorem terms_count (V : ℕ) (terms : Terms V) (hn : (Terms.keys terms).Nodup) :
    terms.length≤2^V := by
  have hh:=hn.length_le_card
  simpa only [Terms.keys,List.length_map,Fintype.card_finset,Fintype.card_fin] using hh

/-- `lem:print`, paper/paper.tex: the literal
canonical Terms serialization has small logarithmic length even when
the actual number of records is exponential. -/
theorem termsWord_bitLength (V bits : ℕ) (terms : Terms V)
    (hn : (Terms.keys terms).Nodup) (hc : ∀t∈terms,t.2.natAbs<2^bits) :
    natBitLength (termsWord terms).length≤V+recordHeight V bits+4 := by
  have hcount:=terms_count V terms hn
  have hhead:=natWord_len_le terms.length terms.length Nat.lt_two_pow_self
  have hsum:=List.sum_le_card_nsmul (terms.map fun t=>(monoWord t).length)
    (recordHeight V bits) (by
      intro value hv
      obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hv
      exact monoWord_length V bits t (hc t ht))
  simp only [List.length_map,smul_eq_mul] at hsum
  have hlen : (termsWord terms).length≤terms.length*(recordHeight V bits+2)+3 := by
    simp only [termsWord,listWord,List.length_append,List.length_flatMap]
    nlinarith only [hhead,hsum]
  have hprod : terms.length*(recordHeight V bits+2)≤2^(V+recordHeight V bits+2) := by
    calc
      _≤2^V*2^(recordHeight V bits+2) :=
        Nat.mul_le_mul hcount Nat.lt_two_pow_self.le
      _=_ := by simp only [←pow_add,Nat.add_assoc]
  have hthree : 3<2^(V+recordHeight V bits+2) := by
    have hh:=Nat.pow_le_pow_right (n:=2) (by decide) (show 2≤V+recordHeight V bits+2 by omega)
    norm_num at hh
    omega
  apply nbl_le_of_lt
  have hbound : (termsWord terms).length<2^(V+recordHeight V bits+3) := by
    have he : 2^(V+recordHeight V bits+3)=2*2^(V+recordHeight V bits+2) := by
      rw [show V+recordHeight V bits+3=(V+recordHeight V bits+2)+1 by omega,pow_succ]
      omega
    omega
  exact hbound

end NearQuarticWires.StageGreedyEntryBounds
