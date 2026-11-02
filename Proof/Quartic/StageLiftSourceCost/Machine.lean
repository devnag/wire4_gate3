import Proof.Quartic.StageLiftSourceCost.Startup
import Proof.Quartic.StageLiftSourceCost.Walks

/-!
# Ordinary-machine price with separate raw-index acquisition

`prop:time`, paper/paper.tex: the full compiled
machine pays setup, actual source loops, structural callees, framing
and teardown. The raw-index term occurs only in startup and input
traversal, separately from the complete original-walk census.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftSourceCost
open NearCubicGates.Close.Cells StageLift

variable {B1 B2 : ℕ}

theorem source_steps_scale (r : Greedy.PrintRequest B1 B2) :
    sourceProgramSteps r ≤ 20000000000000*
      (r.child.cellCall.seed.N^8*(Builder.allGates r.child.call).length^r.child.selected.1.Xmax*
        (sourceScale r)^30+(sourceScale r)^3*((Greedy.printIndexWord r).length+1)) := by
  let S:=sourceScale r
  let M:=(Builder.allGates r.child.call).length^r.child.selected.1.Xmax
  let N:=r.child.cellCall.seed.N^8
  let I:=(Greedy.printIndexWord r).length
  have hs : 1 ≤ S := by have hh:=(sourceScale_small r).1;omega
  have hm : 1 ≤ M := original_tuple_pos r
  have hn : 1 ≤ N := walkCount_pos r
  have hstart:=carrier_startup_scale r
  have hwalk:=all_walk_scale r
  have h3 : S^3 ≤ S^30 := Nat.pow_le_pow_right hs (by decide)
  have hN3:=Nat.mul_le_mul_left N h3
  have hM30:=Nat.mul_le_mul_left (N*S^30) hm
  have hNM0 : 1 ≤ N*M*S^30 := Nat.mul_pos (Nat.mul_pos hn hm) (Nat.pow_pos hs)
  change _ ≤ 1000000*(N*S^3+S^3*(I+1)) at hstart
  change _ ≤ 10000000000000*N*M*S^30 at hwalk
  dsimp only [sourceProgramSteps]
  change _ ≤ 20000000000000*(N*M*S^30+S^3*(I+1))
  nlinarith only [hstart,hwalk,hN3,hM30,hNM0,Nat.zero_le (S^3*(I+1))]

theorem source_machine_scale (r : Greedy.PrintRequest B1 B2) :
    sourceMachineBudget r ≤ 10^19*
      (r.child.cellCall.seed.N^8*(Builder.allGates r.child.call).length^r.child.selected.1.Xmax*
        (sourceScale r)^32+(sourceScale r)^5*((Greedy.printIndexWord r).length+1)) := by
  let S:=sourceScale r
  let M:=(Builder.allGates r.child.call).length^r.child.selected.1.Xmax
  let N:=r.child.cellCall.seed.N^8
  let I:=(Greedy.printIndexWord r).length
  have hs : 1 ≤ S := by have hh:=(sourceScale_small r).1;omega
  have hm : 1 ≤ M := original_tuple_pos r
  have hn : 1 ≤ N := walkCount_pos r
  have hsteps:=source_steps_scale r
  have hinput:=print_input_length r
  have h2 : S^2 ≤ S^30 := Nat.pow_le_pow_right hs (by decide)
  have hN2:=Nat.mul_le_mul_left N h2
  have hM30:=Nat.mul_le_mul_left (N*S^30) hm
  have hI : I+1 ≤ S^3*(I+1) := Nat.le_mul_of_pos_left _ (Nat.pow_pos hs)
  have hsum : sourceProgramSteps r+(Greedy.printInput r).length+1 ≤
      30000000000000*(N*M*S^30+S^3*(I+1)) := by
    change _ ≤ 20000000000000*(N*M*S^30+S^3*(I+1)) at hsteps
    change _ ≤ 70*N*S^2+I at hinput
    nlinarith only [hsteps,hinput,hN2,hM30,hI,Nat.zero_le (S^3*(I+1))]
  calc
    sourceMachineBudget r ≤ 10000*S^2*(sourceProgramSteps r+(Greedy.printInput r).length+1) :=
      source_compiler_bound r _
    _ ≤ 10000*S^2*(30000000000000*(N*M*S^30+S^3*(I+1))) := Nat.mul_le_mul_left _ hsum
    _ ≤ 10^19*(N*M*S^32+S^5*(I+1)) := by
      have hpow30 : S^2*S^30=S^32 := by rw [←pow_add]
      have hpow3 : S^2*S^3=S^5 := by rw [←pow_add]
      calc
        _ = 300000000000000000*(N*M*S^32+S^5*(I+1)) := by
          rw [show 10000*S^2*(30000000000000*(N*M*S^30+S^3*(I+1)))=
            300000000000000000*(N*M*(S^2*S^30)+(S^2*S^3)*(I+1)) by ring,hpow30,hpow3]
        _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

end NearQuarticWires.StageLiftSourceCost
