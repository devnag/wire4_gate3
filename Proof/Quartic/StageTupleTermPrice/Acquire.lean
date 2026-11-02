import Proof.Quartic.StageTupleTermPrice.Codecs

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (natWord_length)
open NearCubicGates.Close.Interfaces
open StageTuple

/-- `prop:time`, paper/paper.tex: the
local scratch clearing bound uses only actual support and signed
coefficient packets, not the complete retained Terms stream. -/
theorem Case.localCapacity_bound (j : Case) :
    monomialLocalCapacity j.width j.support j.term.2≤100*j.small^2 := by
  have hw:=j.small_bounds.2.2.1
  have ha:=j.card_le_small
  have hs:=j.support_word_length
  have hc:=j.coefficient_word_length
  have hb:=NearCubicGates.Close.Dispatch.natBitLength_le_succ j.width
  have hm:=NearCubicGates.Close.Dispatch.natBitLength_le_succ j.support.length
  have hp:=NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le j.support.length
  have hN:=natural_word_length j.width
  have hpos:=j.small_bounds.1
  rw [j.support_length] at hm hp
  unfold monomialLocalCapacity
  simp only [List.sum_cons,List.sum_nil,pow_succ,j.support_length]
  nlinarith only [hw,ha,hs,hc,hb,hm,hp,hN,hpos]

/-- `prop:time`, paper/paper.tex: the
real support copy pays its count decoder, binary header writer and
every original finite variable codec with a source-local polynomial. -/
theorem Case.supportCopy_bound (j : Case) :
    supportCopyCost j.support≤10000*j.small^2 := by
  have hlen : j.support.length≤ j.small := j.support_length.trans_le j.card_le_small
  have hb:=NearCubicGates.Close.Dispatch.natBitLength_le_succ j.support.length
  have hread:=natural_count_readCost_le j.support.length
  have hs:=List.sum_le_card_nsmul (j.support.map fun v=>60*(natWord v).length+60+4)
    (120*j.small+244) (by
      intro x hx
      obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
      have hw:=natural_word_length v
      have hh:=j.support_member v hv
      omega)
  simp only [List.length_map,smul_eq_mul] at hs
  have hsum:=hs.trans (Nat.mul_le_mul_right _ hlen)
  have hp:=j.small_bounds.1
  unfold supportCopyCost NearCubicGates.Close.Codec.copyListCost
  simp only [List.map_map,Function.comp_def]
  nlinarith only [hlen,hb,hread,hsum,hp]

/-- `prop:time`, paper/paper.tex: the
actual source scan, two cache rewinds and ten finite scratch clears
have a structural polynomial clock for every signed coefficient. -/
theorem Case.acquire_bound (j : Case) :
    monomialAcquireCost (monomialLocalCapacity j.width j.support j.term.2)
      j.width j.support j.term.2≤10^7*j.small^2 := by
  have hl:=j.localCapacity_bound
  have hs:=j.supportCopy_bound
  have hw:=j.small_bounds.2.2.1
  have hb:=NearCubicGates.Close.Dispatch.natBitLength_le_succ j.width
  have hword:=j.support_word_length
  have hcoef:=j.coefficient_word_length
  have hnat:=natural_word_length j.width
  have hpos:=j.small_bounds.1
  unfold monomialAcquireCost monomialReadyCost monomialFormatCost
  simp only [frame_length,List.length_append]
  nlinarith only [hl,hs,hw,hb,hword,hcoef,hnat,hpos]

theorem price_acquire : Price Case.small (fun j=>
    monomialAcquireCost (monomialLocalCapacity j.width j.support j.term.2)
      j.width j.support j.term.2) := ⟨10^7,2,Case.acquire_bound⟩

end NearQuarticWires.StageTupleTermPrice
