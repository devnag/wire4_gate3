import Proof.Quartic.StageCert.PolarityPair

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `sec:walks` and `lem:print`, paper/paper.tex: select the actual edge sign before emitting its exact
single signed coefficient token. -/
def emitPolarityCoefficient : St VV MM :=
  .seq selectPolarityPair emitOriginalCoefficient

/-- `lem:print` and `prop:time`, paper/paper.tex: the physical coefficient writer has the original
postfix constant for weight times sign, rather than a larger arithmetic
expression, and preserves every retained source record. -/
theorem emitPolarityCoefficient_run (C : Ctx) (positive negative B : ℕ) (sign : Bool)
    (a : DS VV MM) (hc : Cst a) (hp : a.env cachedPositive=positive)
    (hn : a.env cachedNegative=negative) (hs : a.env selectedTokenBit=sign.toNat)
    (hW : 3≤C.Wd) (hB : natBitLength (((positive:ℤ)-negative).natAbs)≤B)
    (hfit : B+2<2^C.Wd) :
    Hs C emitPolarityCoefficient a (40*B+145) (fun z=>
      z.out=a.out++tokWord (.const (((positive:ℤ)-negative)*Cycle.signValue sign)) ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z ([linearPositive,linearNegative,newtonSignField,newtonMagnitudeField]++
        StageLift.tokenScratch)) := by
  have hid : ((if sign then positive else negative : ℕ):ℤ)-
      (if sign then negative else positive : ℕ)=((positive:ℤ)-negative)*Cycle.signValue sign := by
    cases sign <;> simp [Cycle.signValue,Cycle.choiceSign]
  have hmag : natBitLength ((((if sign then positive else negative : ℕ):ℤ)-
      (if sign then negative else positive : ℕ)).natAbs)≤B := by
    rw [hid,Int.natAbs_mul]
    have hh : (Cycle.signValue sign).natAbs=1 := by cases sign <;> decide
    simpa only [hh,mul_one] using hB
  unfold emitPolarityCoefficient
  apply Hx.hs
  refine Hs.then (selectPolarityPair_run C positive negative sign a hc hp hn hs)
    (fun b ⟨bp,bn,bs,bc,bfr⟩ n1 hn1=>?_)
  refine Hs.last (emitOriginalCoefficient_run C _ _ B b bc bp bn hW hmag hfit)
    (fun z ⟨zo,zs,zc,zfr⟩ n2 hn2=>?_)
  have bo : b.out=a.out := congrArg (fun q=>q.2.1) bs
  have bsource : (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    simp only [DS.sh,Prod.mk.injEq] at bs ⊢
    exact ⟨bs.1,bs.2.2.1,bs.2.2.2.1,bs.2.2.2.2.1,bs.2.2.2.2.2.1,bs.2.2.2.2.2.2⟩
  refine ⟨⟨by simpa only [bo,hid] using zo,zs.trans bsource,zc,
    (bfr.weaken (by simp)).trans (zfr.weaken (by
      intro y hy
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hy ⊢
      tauto))⟩,?_⟩
  omega

end NearQuarticWires.StageCert.Tokens
