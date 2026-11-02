import Proof.Quartic.StageLift.Token

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`(b,c), paper/paper.tex: a literal
original-atom index uses the unchanged integer-formula postfix codec. -/
def emitAtom (value : Fin VV) : St VV MM :=
  StageLift.emitPrefixedVariable (natWord 1) value

/-- `lem:print`(b,c), paper/paper.tex: the atom token
is physically emitted from its numeric original-pool index. -/
theorem emitAtom_run (C : Ctx) (value : Fin VV) (hv : value≠t3) (hJ : value≠vJ)
    (a : DS VV MM) (hc : Cst a) (hW : 2≤C.Wd)
    (hfit : natBitLength (a.env value)+2<2^C.Wd) :
    Hs C (emitAtom value) a (40*natBitLength (a.env value)+50) (fun b =>
      b.out=a.out++tokWord (.var (a.env value)) ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b StageLift.tokenScratch) := by
  have h := StageLift.emitPrefixedVariable_spec C (natWord 1) value hv hJ a hc hW hfit
  unfold emitAtom
  refine h.mono (by rw [show (natWord 1).length=3 by decide]; omega) ?_
  rintro b ⟨bo,br,bc,bf⟩
  exact ⟨by simpa only [tokWord,List.append_assoc] using bo,br,bc,bf⟩

/-- `lem:print`(b,c), paper/paper.tex: a literal
moment exponent is emitted in binary inside its original postfix token. -/
def emitPower (value : Fin VV) : St VV MM :=
  StageLift.emitPrefixedVariable (natWord 6) value

/-- `lem:print`(b,c), paper/paper.tex: the power token
retains its exact exponent and has polynomial binary output cost. -/
theorem emitPower_run (C : Ctx) (value : Fin VV) (hv : value≠t3) (hJ : value≠vJ)
    (a : DS VV MM) (hc : Cst a) (hW : 2≤C.Wd)
    (hfit : natBitLength (a.env value)+2<2^C.Wd) :
    Hs C (emitPower value) a (40*natBitLength (a.env value)+58) (fun b =>
      b.out=a.out++tokWord (.pow (a.env value)) ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b StageLift.tokenScratch) := by
  have h := StageLift.emitPrefixedVariable_spec C (natWord 6) value hv hJ a hc hW hfit
  unfold emitPower
  refine h.mono (by rw [show (natWord 6).length=7 by decide]; omega) ?_
  rintro b ⟨bo,br,bc,bf⟩
  exact ⟨by simpa only [tokWord,List.append_assoc] using bo,br,bc,bf⟩

/-- `lem:print`(b,c), paper/paper.tex: signed mask
coefficients and proposed-chain weights keep both their sign and magnitude. -/
def emitSignedConstant (sign magnitude : Fin VV) : St VV MM :=
  .seq (StageLift.emitPrefixedVariable (natWord 0) sign) (StageRecovery.emitVariable magnitude)

/-- `lem:print`(b,c), paper/paper.tex: an arbitrary
signed integer coefficient is serialized exactly, before any certification
test and without a reduction or natural truncation. -/
theorem emitSignedConstant_run (C : Ctx) (sign magnitude : Fin VV)
    (hs3 : sign≠t3) (hsJ : sign≠vJ) (hm3 : magnitude≠t3)
    (hmT : magnitude∉StageLift.tokenScratch)
    (a : DS VV MM) (hc : Cst a) (hW : 2≤C.Wd) (z : ℤ)
    (hs : a.env sign=(if z<0 then 1 else 0)) (hm : a.env magnitude=z.natAbs)
    (hsfit : natBitLength (a.env sign)+2<2^C.Wd)
    (hmfit : natBitLength (a.env magnitude)+2<2^C.Wd) :
    Hs C (emitSignedConstant sign magnitude) a
      (40*natBitLength (a.env sign)+40*natBitLength z.natAbs+93) (fun b =>
      b.out=a.out++tokWord (.const z) ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b StageLift.tokenScratch) := by
  unfold emitSignedConstant
  have first := (StageLift.emitPrefixedVariable_spec C (natWord 0) sign hs3 hsJ a hc hW hsfit).mono
    (t' := 40*natBitLength (a.env sign)+50)
    (by rw [show (natWord 0).length=3 by decide]; omega) (fun _ h=>h)
  refine (Hs.seq (t1 := 40*natBitLength (a.env sign)+50)
    (t2 := 40*natBitLength z.natAbs+42)
    first ?_).mono
      (by omega) (fun _ h=>h)
  rintro b ⟨bo,br,bconst,bfr⟩
  have bm : b.env magnitude=z.natAbs := (bfr _ hmT).trans hm
  refine (StageRecovery.emitVariable_spec C b bconst magnitude hm3 hW
    (by rw [bfr _ hmT]; exact hmfit)).mono (by rw [bm]) ?_
  rintro d ⟨doo,dr,dconst,dfr⟩
  refine ⟨?_,dr.trans br,dconst,bfr.trans (dfr.weaken (by simp [StageLift.tokenScratch]))⟩
  rw [doo,bo,bm]
  simp only [tokWord,NearCubicGates.Close.Interfaces.intWord,hs,List.append_assoc]

end NearQuarticWires.StageCert.Tokens
