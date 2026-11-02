import Proof.Quartic.StageLiftSourceCost.Reserve
import Proof.Quartic.StageMain.RuntimeSizes

/-!
# Original-header scale of the physical source machine

`prop:time`, paper/paper.tex: arithmetic width,
structural-call reservations and fixed compiler dimensions are
polynomial in original arity, independently of the Gamma table and
raw index suffix lengths.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftSourceCost
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells StageLift

variable {B1 B2 : ℕ}

noncomputable def sourceScale (r : Greedy.PrintRequest B1 B2) : ℕ :=
  let z:=printSourceSizes B1 B2
  let h:=1+natBitLength r.child.call.n
  sourceEnvelope r+1+z.W h+z.Lk h+z.Bk h+z.a1+z.a2+z.a3+z.c1+z.c2+z.c3+
    TSK (StageCert.Tokens.structuralSourceCallee B1 B2)+VV+MM+r.child.call.n+1000

noncomputable def scaleExponent (B1 B2 : ℕ) : ℕ :=
  let z:=printSourceSizes B1 B2
  sourceWidthExponent B1 B2+z.c1+z.c2+z.c3+1

noncomputable def scaleCoefficient (B1 B2 : ℕ) : ℕ :=
  let z:=printSourceSizes B1 B2
  sourceWidthCoefficient B1+z.a1*4^z.c1+z.a2*4^z.c2+z.a3*4^z.c3+
    z.a1+z.a2+z.a3+z.c1+z.c2+z.c3+
    TSK (StageCert.Tokens.structuralSourceCallee B1 B2)+VV+MM+1003

theorem sourceScale_small (r : Greedy.PrintRequest B1 B2) :
    1000 ≤ sourceScale r ∧ sourceEnvelope r+1 ≤ sourceScale r ∧ r.child.call.n+1 ≤ sourceScale r := by
  dsimp only [sourceScale]
  omega

theorem sourceScale_polynomial (r : Greedy.PrintRequest B1 B2) :
    sourceScale r ≤ scaleCoefficient B1 B2*(r.child.call.n+1)^scaleExponent B1 B2 := by
  let z:=printSourceSizes B1 B2
  let b:=r.child.call.n+1
  let d:=scaleExponent B1 B2
  have hb : 1 ≤ b := by dsimp [b];omega
  have hd : 1 ≤ d := by dsimp [d,scaleExponent];omega
  have hE:= (sourceEnvelope_polynomial r).trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hb (show sourceWidthExponent B1 B2 ≤ d by dsimp [d,scaleExponent];omega)))
  have hW:=(StageMain.Runtime.header_power_le z.a1 z.c1 r.child.call.n).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb
      (show z.c1 ≤ d by dsimp [d,scaleExponent,z];omega)))
  have hL:=(StageMain.Runtime.header_power_le z.a2 z.c2 r.child.call.n).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb
      (show z.c2 ≤ d by dsimp [d,scaleExponent,z];omega)))
  have hB:=(StageMain.Runtime.header_power_le z.a3 z.c3 r.child.call.n).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb
      (show z.c3 ≤ d by dsimp [d,scaleExponent,z];omega)))
  have hn : b ≤ b^d := Nat.le_self_pow (by omega) _
  have hp : 1 ≤ b^d := Nat.pow_pos hb
  have hc:=Nat.mul_le_mul_left
    (z.a1+z.a2+z.a3+z.c1+z.c2+z.c3+
      TSK (StageCert.Tokens.structuralSourceCallee B1 B2)+VV+MM+1002) hp
  change sourceEnvelope r+1+z.W (1+natBitLength r.child.call.n)+
    z.Lk (1+natBitLength r.child.call.n)+z.Bk (1+natBitLength r.child.call.n)+
    z.a1+z.a2+z.a3+z.c1+z.c2+z.c3+
    TSK (StageCert.Tokens.structuralSourceCallee B1 B2)+VV+MM+r.child.call.n+1000 ≤ _
  change 2^(z.c1*(1+natBitLength r.child.call.n))*z.a1 ≤ _ at hW
  change 2^(z.c2*(1+natBitLength r.child.call.n))*z.a2 ≤ _ at hL
  change 2^(z.c3*(1+natBitLength r.child.call.n))*z.a3 ≤ _ at hB
  dsimp only [Sz.W,Sz.Lk,Sz.Bk,scaleCoefficient]
  change _ ≤ (sourceWidthCoefficient B1+z.a1*4^z.c1+z.a2*4^z.c2+z.a3*4^z.c3+
    z.a1+z.a2+z.a3+z.c1+z.c2+z.c3+
    TSK (StageCert.Tokens.structuralSourceCallee B1 B2)+VV+MM+1003)*b^d
  change r.child.call.n+1 ≤ b^d at hn
  nlinarith only [hE,hW,hL,hB,hn,hc,hp]

theorem source_header (r : Greedy.PrintRequest B1 B2) :
    leadOnes (Greedy.printInput r)=1+natBitLength r.child.call.n := by
  simpa only [List.append_nil] using printInput_header_width r []

theorem source_compiler_bound (r : Greedy.PrintRequest B1 B2) (N : ℕ) :
    langBudget (StageCert.Tokens.structuralSourceCallee B1 B2) (printSourceSizes B1 B2)
      VV MM (Greedy.printInput r) N ≤ 10000*(sourceScale r)^2*(N+(Greedy.printInput r).length+1) := by
  have hb:=sourceScale_small r
  have hn:=NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self r.child.call.n
  apply StageMain.Runtime.langBudget_le
  all_goals try rw [source_header]
  all_goals dsimp only [sourceScale] at *
  all_goals omega

end NearQuarticWires.StageLiftSourceCost
