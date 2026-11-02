import Proof.Quartic.StageTupleTermPrice.Polynomial
import Proof.Gates.Expand.Cost2

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (natWord_length)
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms.SInt (encS)
open StageTuple

/-- `prop:time`, paper/paper.tex: canonical
binary source lengths depend on bit height, never a unary expansion
of a signed coefficient's numerical magnitude. -/
theorem natural_word_length (n : ℕ) : (natWord n).length≤2*n+3 := by
  rw [natWord_length]
  have hh:=NearCubicGates.Close.Dispatch.natBitLength_le_succ n
  omega

theorem Price.natBits {I : Type} {s f : I→ℕ} (hs : ∀j,1≤ s j) (hf : Price s f) :
    Price s (fun j=> natBitLength (f j)) :=
  (hf.add hs (Price.constant s 1)).mono
    (fun j=> NearCubicGates.Close.Dispatch.natBitLength_le_succ (f j))

theorem Price.natWord {I : Type} {s f : I→ℕ} (hs : ∀j,1≤ s j) (hf : Price s f) :
    Price s (fun j=>(natWord (f j)).length) := by
  simpa only [natWord_length] using
    (((Price.constant s 2).mul (hf.natBits hs)).add hs (Price.constant s 1))

theorem Case.support_word_length (j : Case) :
    (listWord natWord j.support).length≤10*j.small^2 := by
  have hlen : j.support.length≤ j.small := j.support_length.trans_le j.card_le_small
  have hh:=List.sum_le_card_nsmul (j.support.map fun v=>(natWord v).length)
    (2*j.small+3) (by
      intro x hx
      obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
      exact (natural_word_length v).trans (by have h:=j.support_member v hv;omega))
  simp only [List.length_map,smul_eq_mul] at hh
  have hsum:=hh.trans (Nat.mul_le_mul_right _ hlen)
  have hhead:=natural_word_length j.support.length
  have hpos:=j.small_pos
  simp only [listWord,List.length_append,List.length_flatMap]
  nlinarith only [hsum,hhead,hlen,hpos]

theorem Case.coefficient_word_length (j : Case) :
    (intWord j.term.2).length≤10*j.small := by
  have hfit:=j.request.coefficient_fit j.term j.term_mem
  change encS j.term.2<2^j.width at hfit
  have ha : j.term.2.natAbs<2^j.width := by unfold encS at hfit;omega
  have hb:=NearCubicGates.Close.Expand.Layout.nbl_le_of_lt j.term.2.natAbs j.width ha
  have hsign : (natWord (if j.term.2<0 then 1 else 0)).length=3 := by split_ifs <;> decide
  simp only [intWord,List.length_append,hsign,natWord_length]
  have hw:=j.small_bounds.2.2.1
  have hs:=j.small_pos
  omega

theorem price_supportLength : Price Case.small (fun j=> j.support.length) :=
  Price.scalar (fun j=> j.support_length.trans_le j.card_le_small)

theorem price_supportWordLength : Price Case.small (fun j=>(listWord natWord j.support).length) :=
  ⟨10,2,Case.support_word_length⟩

theorem price_coefficientWordLength : Price Case.small (fun j=>(intWord j.term.2).length) :=
  ⟨10,1,by simpa only [pow_one] using Case.coefficient_word_length⟩

theorem price_width : Price Case.small Case.width := Price.scalar (fun j=> j.small_bounds.2.2.1)

end NearQuarticWires.StageTupleTermPrice
