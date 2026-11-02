import Proof.Quartic.StageLift.Literal

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the output
serializer changes only its fixed binary printer scratch variables. -/
def tokenScratch : List (Fin VV) := [t3, t5, t6, t7, t8, t9, vJ]

/-- `lem:print`, paper/paper.tex: fixed postfix
tags precede the computed binary payload of a variable or exponent. -/
def emitPrefixedVariable (headWord : List Bool) (value : Fin VV) : St VV MM :=
  .seq (emitLiteral headWord) (StageRecovery.emitVariable value)

/-- `lem:print`, paper/paper.tex: computed token
payloads use their original natural codec, with cost proportional to
their binary length and no conversion into unary counters. -/
theorem emitPrefixedVariable_spec (C : Ctx) (headWord : List Bool) (value : Fin VV)
    (hvalue : value ≠ t3) (hvalueJ : value ≠ vJ)
    (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd)
    (hfit : natBitLength (a.env value) + 2 < 2 ^ C.Wd) :
    Hs C (emitPrefixedVariable headWord value) a
      (2 * headWord.length + 40 * natBitLength (a.env value) + 44) (fun b =>
      b.out = a.out ++ headWord ++ natWord (a.env value) ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b tokenScratch) := by
  unfold emitPrefixedVariable
  refine (Hs.seq (t2 := 40 * natBitLength (a.env value) + 42)
    (emitLiteral_spec C headWord a hc) fun b ⟨ho, hr, hbc, hf⟩ => ?_).mono
      (by omega) (fun _ h => h)
  have hb : b.env value = a.env value := hf value (by simp [hvalueJ])
  have he := StageRecovery.emitVariable_spec C b hbc value hvalue hW (by rw [hb]; exact hfit)
  rw [hb] at he
  refine he.mono le_rfl ?_
  rintro d ⟨hdo, hdr, hdc, hdf⟩
  exact ⟨by rw [hdo, ho], hdr.trans hr, hdc,
    Fr.trans (Fr.weaken hf (by simp [tokenScratch]))
      (Fr.weaken hdf (by simp [tokenScratch]))⟩

/-- `lem:print`, paper/paper.tex: a nonnegative
reduced constant is serialized with the zero sign field. -/
def emitNaturalConstant (value : Fin VV) : St VV MM :=
  emitPrefixedVariable (natWord 0 ++ natWord 0) value

/-- `lem:print`, paper/paper.tex: the actual
constant writer has exactly the canonical integer postfix codec. -/
theorem emitNaturalConstant_spec (C : Ctx) (value : Fin VV)
    (hvalue : value ≠ t3) (hvalueJ : value ≠ vJ)
    (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd)
    (hfit : natBitLength (a.env value) + 2 < 2 ^ C.Wd) :
    Hs C (emitNaturalConstant value) a (40 * natBitLength (a.env value) + 56) (fun b =>
      b.out = a.out ++ tokWord (.const (a.env value : ℤ)) ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b tokenScratch) := by
  have he := emitPrefixedVariable_spec C (natWord 0 ++ natWord 0) value
    hvalue hvalueJ a hc hW hfit
  unfold emitNaturalConstant
  refine he.mono (by
    have hl : (natWord 0 ++ natWord 0).length = 6 := by decide
    omega) ?_
  rintro b ⟨ho, hr, hbc, hf⟩
  exact ⟨by simpa [tokWord, NearCubicGates.Close.Interfaces.intWord, List.append_assoc] using ho,
    hr, hbc, hf⟩

end NearQuarticWires.StageLift
