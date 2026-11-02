import Proof.Quartic.StageCert.MomentRuntimeScale

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageMain

/-- `prop:time`, paper/paper.tex: all allocator
and structural-callee exponents are fixed once before any original
call, so their sum gives one runtime-scale arity exponent. -/
noncomputable def momentRuntimeExponent (B1 B2 : ℕ) : ℕ :=
  let z := momentSourceSizes B1 B2
  z.c1+z.c2+z.c3+momentScaleExponent B1 B2+1

/-- `prop:time`, paper/paper.tex: every fixed
compiler dimension and allocator coefficient enters the actual runtime
constant, including the concrete shared structural machine's tapes. -/
noncomputable def momentRuntimeCoefficient (B1 B2 : ℕ) : ℕ :=
  let z := momentSourceSizes B1 B2
  momentScaleCoefficient B1+z.a1*4^z.c1+z.a2*4^z.c2+z.a3*4^z.c3+
    z.a1+z.c1+z.a2+z.c2+z.a3+z.c3+
    TSK (structuralSourceCallee B1 B2)+VV+MM+1001

/-- `prop:time`, paper/paper.tex: the complete
actual source/compiler runtime scale has one fixed original-arity
polynomial bound, uniformly over all proposed witness contents. -/
theorem MomentRequest.runtimeScale_arity {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.runtimeScale≤ momentRuntimeCoefficient B1 B2*(r.call.n+1)^momentRuntimeExponent B1 B2 := by
  let z := momentSourceSizes B1 B2
  let E := momentRuntimeExponent B1 B2
  let Z := (r.call.n+1)^E
  let F := z.a1+z.c1+z.a2+z.c2+z.a3+z.c3+
    TSK (structuralSourceCallee B1 B2)+VV+MM+1000
  have hE : 1≤E := by dsimp only [E,momentRuntimeExponent]; omega
  have hZ : 1≤Z := Nat.pow_pos (Nat.succ_pos _)
  have hn : r.call.n≤Z := (Nat.le_succ _).trans (Nat.le_self_pow (by omega : E≠0) _)
  have hF : F≤F*Z := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left F hZ
  have hbody : r.bodyScale ≤ momentScaleCoefficient B1*Z :=
    r.bodyScale_arity.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
      (by dsimp only [E,momentRuntimeExponent,z]; omega)))
  have hW : z.W (1+natBitLength r.call.n)≤(z.a1*4^z.c1)*Z := by
    have hh := Runtime.header_power_le z.a1 z.c1 r.call.n
    exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
      (by dsimp only [E,momentRuntimeExponent,z]; omega)))
  have hL : z.Lk (1+natBitLength r.call.n)≤(z.a2*4^z.c2)*Z := by
    have hh := Runtime.header_power_le z.a2 z.c2 r.call.n
    exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
      (by dsimp only [E,momentRuntimeExponent,z]; omega)))
  have hB : z.Bk (1+natBitLength r.call.n)≤(z.a3*4^z.c3)*Z := by
    have hh := Runtime.header_power_le z.a3 z.c3 r.call.n
    exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
      (by dsimp only [E,momentRuntimeExponent,z]; omega)))
  have heq : r.runtimeScale=r.bodyScale+z.W (1+natBitLength r.call.n)+
      z.Lk (1+natBitLength r.call.n)+z.Bk (1+natBitLength r.call.n)+F+r.call.n := by
    dsimp only [MomentRequest.runtimeScale,F,z]
    ring
  rw [heq]
  calc
    _ ≤ momentScaleCoefficient B1*Z+(z.a1*4^z.c1)*Z+(z.a2*4^z.c2)*Z+
        (z.a3*4^z.c3)*Z+F*Z+Z := by omega
    _ = momentRuntimeCoefficient B1 B2*Z := by
      dsimp only [momentRuntimeCoefficient,F,z]
      ring

end NearQuarticWires.StageCert.Tokens
