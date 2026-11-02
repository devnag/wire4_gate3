import Proof.Quartic.StageTupleTermPrice.Elements
import Proof.Quartic.StageTupleTermPrice.Records
import Proof.Quartic.StageTupleTermPrice.Support
import Proof.Quartic.StageTupleTermPrice.Weighted

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open StageTuple

/-- `prop:time`, paper/paper.tex: actual
measured native reply and selected-atom caches are erased once; no
previous tuple-history or output prefix is part of this clock. -/
theorem Step.cleanup_bound (j : Step) :
    nativeCleanupCost j.supportRequest.output (natWord j.tupleRequest.children.length)
      (fieldRecords j.tupleRequest.L j.tupleRequest.children)≤100000*j.small^3*j.square := by
  have hQ:=j.square_pos
  have hS:=j.small_pos
  have hK:=j.square_elements.1
  have hL:=j.dimensions.1
  have hN:=j.dimensions.2.1
  have ha:=j.support_packet_bounds.2.2.1
  have hnat:=natural_word_length j.tupleRequest.children.length
  have hrecords : ((fieldRecords j.tupleRequest.L j.tupleRequest.children).flatMap frame).length≤
      j.square*j.small*(2*j.small+1) := by
    rw [field_records_length _ _ _ j.tupleRequest.children_length]
    exact Nat.mul_le_mul (Nat.mul_le_mul hK hN) (by omega)
  have h0 : j.square≤j.small^3*j.square:=Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
  have h1 : j.small*j.square≤j.small^3*j.square:=Nat.mul_le_mul_right _ (Nat.le_self_pow (by decide) _)
  have h2 : j.small^2*j.square≤j.small^3*j.square:=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hS (by decide))
  have hatom : j.small≤j.small*j.square:=Nat.le_mul_of_pos_right _ (by omega)
  unfold nativeCleanupCost
  simp only [frame_length,List.length_append]
  nlinarith only [hrecords,hnat,ha,hK,hQ,h0,h1,h2,hatom]

/-- `prop:time`, paper/paper.tex: real
child/tuple counter maintenance is additive and retains the same
actual support square, without any new child-census power. -/
theorem Step.counter_bound (j : Step) :
    100*(j.tupleRequest.children.length*j.tupleRequest.tuples.length+j.tupleRequest.children.length+
      j.tupleRequest.tuples.length+(j.monomial.request.rowDimension+1)+1)≤1000*j.small*j.square := by
  have hh:=j.square_elements
  have hQ:=j.square_pos
  have hS:=j.small_pos
  have hN:=j.monomial.small_bounds.2.2.2.1
  change j.monomial.request.rowDimension+1≤j.small at hN
  have h0 : j.square≤j.small*j.square:=Nat.le_mul_of_pos_left _ (by omega)
  have h1 : j.small≤j.small*j.square:=Nat.le_mul_of_pos_right _ (by omega)
  nlinarith only [hh.1,hh.2.1,hh.2.2.1,hQ,hN,h0,h1]

theorem price_cleanup : WeightedPrice Step.small Step.square (fun j=>
    nativeCleanupCost j.supportRequest.output (natWord j.tupleRequest.children.length)
      (fieldRecords j.tupleRequest.L j.tupleRequest.children)) := ⟨100000,3,Step.cleanup_bound⟩

theorem price_counters : WeightedPrice Step.small Step.square (fun j=>
    100*(j.tupleRequest.children.length*j.tupleRequest.tuples.length+j.tupleRequest.children.length+
      j.tupleRequest.tuples.length+(j.monomial.request.rowDimension+1)+1)) :=
  ⟨1000,1,by simpa only [pow_one] using Step.counter_bound⟩

end NearQuarticWires.StageTupleTermPrice
