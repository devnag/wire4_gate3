import Proof.Quartic.StageCert.CoefficientNormalize

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `eq:testE`, `eq:testPhi` and `lem:print`, paper/paper.tex: physically normalize and emit the original
single signed integer constant, preserving its literal AST and formal mass. -/
def emitOriginalCoefficient : St VV MM :=
  .seq normalizeLinearCoefficient (emitSignedConstant newtonSignField newtonMagnitudeField)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual coefficient token agrees byte for byte with
the original signed formula codec on every proposed chain, including
exact cancellation and negative coefficients before certification. -/
theorem emitOriginalCoefficient_run (C : Ctx) (positive negative B : ℕ)
    (a : DS VV MM) (hc : Cst a) (hp : a.env linearPositive=positive)
    (hn : a.env linearNegative=negative) (hW : 3≤C.Wd)
    (hB : natBitLength (((positive:ℤ)-negative).natAbs)≤B) (hfit : B+2<2^C.Wd) :
    Hs C emitOriginalCoefficient a (40*B+140) (fun z=>
      z.out=a.out++tokWord (.const ((positive:ℤ)-negative)) ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z ([newtonSignField,newtonMagnitudeField]++StageLift.tokenScratch)) := by
  have h8 : 8≤2^C.Wd := by
    have hh := Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide) hW
    norm_num at hh
    exact hh
  unfold emitOriginalCoefficient
  apply Hx.hs
  refine Hs.then (normalizeLinearCoefficient_run C positive negative a hc hp hn)
    (fun b ⟨bsign,bmag,bs,bc,bfr⟩ n1 hn1=>?_)
  have hsign : natBitLength (b.env newtonSignField)≤1 := by
    rw [bsign]
    split_ifs <;> decide
  refine Hs.last (emitSignedConstant_run C newtonSignField newtonMagnitudeField
    (by decide) (by decide) (by decide) (by decide) b bc (by omega)
    ((positive:ℤ)-negative) bsign bmag (by omega) (by rw [bmag]; omega))
    (fun z ⟨zo,zs,zc,zfr⟩ n2 hn2=>?_)
  have bo : b.out=a.out := congrArg (fun q=>q.2.1) bs
  have bsource : (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    simp only [DS.sh,Prod.mk.injEq] at bs ⊢
    exact ⟨bs.1,bs.2.2.1,bs.2.2.2.1,bs.2.2.2.2.1,bs.2.2.2.2.2.1,bs.2.2.2.2.2.2⟩
  refine ⟨⟨by simpa only [bo] using zo,zs.trans bsource,zc,
    (bfr.weaken (by simp)).trans (zfr.weaken (by
      intro y hy
      simp only [List.mem_append,List.mem_cons] at hy ⊢
      exact Or.inr hy))⟩,?_⟩
  omega

end NearQuarticWires.StageCert.Tokens
