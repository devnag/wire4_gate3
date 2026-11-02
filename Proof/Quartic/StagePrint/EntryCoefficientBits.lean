import Proof.Quartic.StagePrint.EntryWidth

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.GreedyEntry

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells StageFormulaMetadata

/-- `lem:print`, paper/paper.tex: exact mode
retains its actual coefficient-bit bound, while modular mode computes
the bit height of the actual modulus by binary halving. -/
def coefficientBitsProgram (modular : Bool) : St VV MM :=
  if modular then .seq (naturalLength modulusVar)
    (.seq (.op (.copy coefficientBitsVar fieldBytesVar)) (.op (.half coefficientBitsVar)))
  else .op (.copy coefficientBitsVar modulusVar)

/-- `lem:print`, paper/paper.tex: scale
processing is logarithmic in its binary value and includes the zero
case, without a loop over a modulus or a coefficient bound. -/
theorem coefficientBitsProgram_run (C : Ctx) (modular : Bool) (scale : ℕ)
    (a : DS VV MM) (hc : Cst a) (hs : a.env modulusVar=scale)
    (hfit : (NearCubicWires.RepairRepresentation.natWord scale).length<2^C.Wd) :
    Hs C (coefficientBitsProgram modular) a (5*natBitLength scale+30) (fun b =>
      b.env coefficientBitsVar=(if modular then natBitLength scale else scale) ∧
      b.sh=a.sh ∧ Cst b ∧ Fr a b [aw0,fieldBytesVar,coefficientBitsVar,vJ]) := by
  cases modular with
  | false=>
    unfold coefficientBitsProgram
    refine (hs_copy C coefficientBitsVar modulusVar a (by decide)).mono (by omega) ?_
    rintro b rfl
    exact ⟨by change a.env modulusVar=scale;exact hs,rfl,
      Cst.of_fr hc (Fr.set a _ (T:=[coefficientBitsVar]) (by simp)) (by decide),
      Fr.set a _ (by simp)⟩
  | true=>
    unfold coefficientBitsProgram
    have er:=naturalLength_spec C modulusVar (by decide) a hc (by rwa [hs])
    rw [hs] at er
    refine (Hs.seq (t2:=3) er fun b ⟨bl,bsh,bc,bfr⟩ => ?_).mono (by omega) (fun _ h=>h)
    refine Hs.seq (t2:=1) (hs_copy C coefficientBitsVar fieldBytesVar b (by decide)) fun d hd => ?_
    subst d
    refine (hs_half C coefficientBitsVar _).mono le_rfl ?_
    rintro d rfl
    have hfr : Fr b ((b.set coefficientBitsVar (b.env fieldBytesVar)).set coefficientBitsVar
        ((b.set coefficientBitsVar (b.env fieldBytesVar)).env coefficientBitsVar/2))
        [aw0,fieldBytesVar,coefficientBitsVar,vJ] :=
      (Fr.set b _ (by simp)).trans (Fr.set _ _ (by simp))
    refine ⟨?_,bsh,Cst.of_fr bc hfr (by decide),
      (bfr.weaken (by simp)).trans hfr⟩
    change b.env fieldBytesVar/2=natBitLength scale
    rw [bl,natWord_length]
    omega

end NearQuarticWires.StagePrint.GreedyEntry
