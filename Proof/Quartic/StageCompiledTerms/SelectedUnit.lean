import Proof.Quartic.StageCompiledTerms.UnitBudget

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires
open StageLiftSourceCost

/-- `prop:time`, paper/paper.tex: a fixed
power of an original-arity polynomial is again a fixed polynomial. -/
theorem power_scale_bound (S A b e k : ℕ) (h : S≤A*b^e) :
    S^k≤A^k*b^(k*e) := by
  have hp:=Nat.pow_le_pow_left h k
  rw [mul_pow,←pow_mul,Nat.mul_comm e k] at hp
  exact hp

/-- `prop:time`, paper/paper.tex: scalar
polynomial factors commute with the selected column census. -/
theorem scalar_reassociate (a c b z : ℕ) : a*(c*b)*z=(a*c)*(z*b) := by ac_rfl

/-- `prop:time`, paper/paper.tex: independent
source, compiler and loop costs add under the same walk census. -/
theorem assemble_unit_bound (N R U Z C0 C1 a b c : ℕ)
    (hR : N*R≤C0*Z) (hU : N*U≤C1*Z) (hN : N≤Z) :
    N*(a*R+b*U+c)≤(a*C0+b*C1+c)*Z := by
  calc N*(a*R+b*U+c)=a*(N*R)+b*(N*U)+c*N := by ring
    _≤a*(C0*Z)+b*(C1*Z)+c*Z :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left a hR)
        (Nat.mul_le_mul_left b hU)) (Nat.mul_le_mul_left c hN)
    _=(a*C0+b*C1+c)*Z := by ring

/-- `prop:time`, paper/paper.tex: all
source/compiler constants depend only on the admitted fixed precisions. -/
noncomputable def unitCoefficient (B1 B2 : ℕ) : ℕ :=
  10^50*(7000000000000^8*(scaleCoefficient B1 B2)^240)+
    4*StageRecovery.selectedCompilerConstant B1+100

/-- `prop:time`, paper/paper.tex: the
ordinary source and actual modular compiler contribute fixed original
arity polynomial degrees, without altering the selected degree guard. -/
noncomputable def unitExponent (B1 B2 : ℕ) : ℕ :=
  240*scaleExponent B1 B2+StageRecovery.selectedCompilerExponent B1+1

/-- `prop:time`, paper/paper.tex: summing
the actual source/formatter/compiler cost over every original walk
fits one selected column count times a fixed arity polynomial. -/
theorem unitBudget_selected {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    r.child.cellCall.seed.N^8*unitBudget r≤unitCoefficient B1 B2*
      2^(r.child.call.n-r.child.selected.1.k)*(r.child.call.n+1)^unitExponent B1 B2 := by
  let b:=r.child.call.n+1
  let E:=unitExponent B1 B2
  let Z:=2^(r.child.call.n-r.child.selected.1.k)*b^E
  let C:=7000000000000^8*(scaleCoefficient B1 B2)^240
  have hb : 1≤b := by dsimp [b];omega
  have hEraw : 240*scaleExponent B1 B2≤E := by dsimp [E,unitExponent];omega
  have hEcompiler : StageRecovery.selectedCompilerExponent B1≤E := by dsimp [E,unitExponent];omega
  have hs:=power_scale_bound (sourceScale r) (scaleCoefficient B1 B2) b
    (scaleExponent B1 B2) 240 (sourceScale_polynomial r)
  have hsource : r.child.cellCall.seed.N^8*(sourcePacketBound r)^8≤C*Z := by
    calc _≤7000000000000^8*(sourceScale r)^240*2^(r.child.call.n-r.child.selected.1.k) :=
        sourcePacketBound_power_reserve r
      _≤7000000000000^8*((scaleCoefficient B1 B2)^240*b^(240*scaleExponent B1 B2))*
          2^(r.child.call.n-r.child.selected.1.k) := by
            exact Nat.mul_le_mul_right (2^(r.child.call.n-r.child.selected.1.k))
              (Nat.mul_le_mul_left (7000000000000^8) hs)
      _=C*(2^(r.child.call.n-r.child.selected.1.k)*b^(240*scaleExponent B1 B2)) := by
        exact scalar_reassociate (7000000000000^8) ((scaleCoefficient B1 B2)^240)
          (b^(240*scaleExponent B1 B2)) (2^(r.child.call.n-r.child.selected.1.k))
      _≤C*Z := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right hb hEraw))
  have hcompiler : r.child.cellCall.seed.N^8*unitCompilerBound r≤
      StageRecovery.selectedCompilerConstant B1*Z := by
    calc _≤StageRecovery.selectedCompilerConstant B1*2^(r.child.call.n-r.child.selected.1.k)*
        (r.child.call.n+1)^StageRecovery.selectedCompilerExponent B1 := unitCompilerBound_selected r
      _≤StageRecovery.selectedCompilerConstant B1*2^(r.child.call.n-r.child.selected.1.k)*b^E :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb hEcompiler)
      _=StageRecovery.selectedCompilerConstant B1*Z := Nat.mul_assoc _ _ _
  have hcount : r.child.cellCall.seed.N^8≤Z :=
    (walkCount_le_columns r).trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos hb))
  have hfinal : r.child.cellCall.seed.N^8*unitBudget r≤unitCoefficient B1 B2*Z :=
    assemble_unit_bound (r.child.cellCall.seed.N^8) ((sourcePacketBound r)^8)
      (unitCompilerBound r) Z C (StageRecovery.selectedCompilerConstant B1)
      (10^50) 4 100 hsource hcompiler hcount
  exact hfinal.trans_eq (Nat.mul_assoc _ _ _).symm

end NearQuarticWires.StageCompiledTerms
