import Proof.Quartic.StageCert.NewtonProgram
import Proof.Quartic.StageCert.FormulaTokens

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: a Newton coefficient is computed from the retained degree
and cutoff and then emitted in the literal signed integer token codec. -/
def emitNewton : St VV MM :=
  .seq computeNewton (emitSignedConstant newtonSignField newtonMagnitudeField)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the actual emitted token contains the full original Newton
coefficient, with no modular reduction and no omitted zero branch. -/
theorem emitNewton_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (tau index B : ℕ) (ht : a.env newtonTau=tau) (hi : a.env newtonIndex=index)
    (hwidth : 2*index+2≤C.Wd) (hW : 3≤C.Wd)
    (hB : natBitLength (Mask.newtonCoeff tau index).natAbs≤B) (hfit : B+2<2^C.Wd) :
    Hs C emitNewton a (17*index+40*B+250) (fun z=>
      z.out=a.out++tokWord (.const (Mask.newtonCoeff tau index)) ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z (newtonScratch++StageLift.tokenScratch)) := by
  have hsbits : natBitLength (if Mask.newtonCoeff tau index<0 then 1 else 0)≤1 := by
    split <;> norm_num [natBitLength]
  have h8 : 8≤2^C.Wd := by
    have hh := Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide) hW
    norm_num at hh
    exact hh
  unfold emitNewton
  refine (Hs.seq (t1 := 17*index+30) (t2 := 40*B+133)
    (computeNewton_original C a hc tau index ht hi hwidth) ?_).mono (by omega) (fun _ h=>h)
  rintro b ⟨bs,bm,bsh,bc,bfr⟩
  refine (emitSignedConstant_run C newtonSignField newtonMagnitudeField
    (by decide) (by decide) (by decide) (by decide) b bc (by omega)
    (Mask.newtonCoeff tau index) bs bm (by rw [bs]; omega)
    (by rw [bm]; omega)).mono (by rw [bs]; omega) ?_
  rintro z ⟨zo,zr,zc,zfr⟩
  have bout : b.out=a.out := congrArg (fun q=>q.2.1) bsh
  have bsrc : (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=
      (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    simp only [DS.sh,Prod.mk.injEq] at bsh
    simp only [Prod.mk.injEq]
    exact ⟨bsh.1,bsh.2.2.1,bsh.2.2.2.1,bsh.2.2.2.2.1,bsh.2.2.2.2.2.1,bsh.2.2.2.2.2.2⟩
  exact ⟨by simpa only [bout] using zo,zr.trans bsrc,zc,
    (bfr.weaken (by intro x hx; exact List.mem_append_left _ hx)).trans
      (zfr.weaken (by intro x hx; exact List.mem_append_right _ hx))⟩

end NearQuarticWires.StageCert.Tokens
