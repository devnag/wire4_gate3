import Proof.Quartic.StageLiftSourceCost.Scale
import Proof.Quartic.StageMain.RuntimeWords
import Proof.Quartic.StageLift.GammaEnvelope
import Proof.Quartic.StageCertTests.ParameterReadCost

/-!
# Actual source-word lengths

`cor:conditional`, `lem:print` and `prop:time`, paper/paper.tex: original preparation
bytes have polynomial size, and each actual Gamma entry has polynomial
binary length. The arbitrary raw index remains a separate suffix.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftSourceCost
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces StageLift

variable {B1 B2 : ℕ}

theorem source_word_lengths (r : Greedy.PrintRequest B1 B2) :
    (preparedWordOf r).length ≤ sourceScale r ∧
    (callWord r.child.call).length ≤ sourceScale r ∧
    (Program.parametersWord r.child.selected.1).length ≤ sourceScale r ∧
    (preparedPrefixWord r.child.call r.child.selected.1).length ≤ sourceScale r ∧
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length ≤ sourceScale r := by
  have hP : (preparedWordOf r).length ≤ sourceScale r :=
    (StageLiftMasks.prepared_length_le r).trans ((Nat.le_succ _).trans (sourceScale_small r).2.1)
  have h:=StageMain.Runtime.compact_lengths r.child.call r.child.selected.1
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness)
  exact ⟨hP,h.1.trans hP,h.2.1.trans hP,h.2.2.1.trans hP,h.2.2.2.trans hP⟩

theorem gamma_table_length (r : Greedy.PrintRequest B1 B2) :
    (Greedy.gammaTable r.child).length=r.child.cellCall.seed.N^8 := by
  simp only [Greedy.gammaTable,List.length_map,Greedy.walkList_length]
  rfl

theorem gamma_entry_word (r : Greedy.PrintRequest B1 B2) (z : ℤ)
    (hz : z∈Greedy.gammaTable r.child) :
    (NearCubicGates.Close.Interfaces.intWord z).length ≤ 2*(sourceScale r)^2+4 := by
  obtain ⟨w,_hw,rfl⟩:=List.mem_map.mp hz
  have hb:=print_gamma_binary_width r w
  have hp:=Nat.pow_le_pow_left (sourceScale_small r).2.1 2
  have hs : (natWord (if r.child.cellCall.walkWeight r.child.seedPrefix w<0 then 1 else 0)).length=3 := by
    split <;> decide
  simp only [NearCubicGates.Close.Interfaces.intWord,List.length_append,hs,natWord_length]
  omega

theorem gamma_word_length (r : Greedy.PrintRequest B1 B2) :
    (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).length ≤ 
      30*r.child.cellCall.seed.N^8*(sourceScale r)^2 := by
  let S:=sourceScale r
  let N:=r.child.cellCall.seed.N^8
  have hs : 1 ≤ S := by have hh:=(sourceScale_small r).1;omega
  have hn : 1 ≤ N := walkCount_pos r
  have hb:=source_walk_counter_bits r
  have hE:=(sourceScale_small r).2.1
  have hf:=StageMain.CallSize.flatMap_length_le NearCubicGates.Close.Interfaces.intWord
    (Greedy.gammaTable r.child) (2*S^2+4) (gamma_entry_word r)
  rw [gamma_table_length] at hf
  have hS1 : S ≤ S^2 := Nat.le_self_pow (by decide) _
  have hS2 : 1 ≤ S^2 := Nat.pow_pos hs
  have hN1 := Nat.mul_le_mul_left N hS2
  have hNS := Nat.mul_le_mul_right (S^2) hn
  simp only [listWord,List.length_append,natWord_length,gamma_table_length]
  change _ ≤ 30*N*S^2
  change (List.flatMap NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).length ≤ N*(2*S^2+4) at hf
  change natBitLength N ≤ 8*sourceEnvelope r+1 at hb
  change sourceEnvelope r+1 ≤ S at hE
  nlinarith only [hf,hb,hE,hS1,hN1,hNS]

theorem print_input_length (r : Greedy.PrintRequest B1 B2) :
    (Greedy.printInput r).length ≤ 
      70*r.child.cellCall.seed.N^8*(sourceScale r)^2+(Greedy.printIndexWord r).length := by
  have hp:=(source_word_lengths r).1
  have hg:=gamma_word_length r
  have hs : 1 ≤ sourceScale r := by have hh:=(sourceScale_small r).1;omega
  have hn:=walkCount_pos r
  have hS1 : sourceScale r ≤ (sourceScale r)^2 := Nat.le_self_pow (by decide) _
  have hNS:=Nat.mul_le_mul_right ((sourceScale r)^2) hn
  have hN1 : 1 ≤ r.child.cellCall.seed.N^8*(sourceScale r)^2 := Nat.mul_pos hn (Nat.pow_pos hs)
  rw [Greedy.printInput,←preparedWordOf_eq_prepWord]
  simp only [Greedy.gammaTableWord,List.length_append,frame_length]
  nlinarith only [hp,hg,hS1,hNS,hN1]

end NearQuarticWires.StageLiftSourceCost
