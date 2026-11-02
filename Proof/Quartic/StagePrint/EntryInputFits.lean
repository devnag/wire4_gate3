import Proof.Quartic.StagePrint.EntrySizing
import Proof.Quartic.StagePrint.DenseWidth

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- `imp:partition` and `lem:print`, paper/paper.tex: the original four geometry codecs are retained as
bytes, independently of the per-walk native output width. -/
def Request.geometryField {modular : Bool} (r : Request modular) : List Bool :=
  [r.header.call.n,r.header.parameters.r,r.header.parameters.b,r.header.parameters.s].flatMap natWord

/-- `lem:print`, paper/paper.tex: the physical
packing arithmetic has exactly the actual native row dimension. -/
theorem Request.stackWidth_actual {modular : Bool} (r : Request modular) :
    r.termRequest.stackWidth=NativeWidth.packedBits r.toRowContext.nativeFieldWidth
      (2*((r.header.call.n+1)/2)) r.degree r.coefficientBits := by
  change NativeWidth.packedBits _ (2*PrimT.C4Geo.width r.header.prepared.starParams) _ _=_
  rw [native_width_eq_half]
  rfl

/-- `lem:print`, paper/paper.tex: every retained
finite field is a literal component of the actual cold formatter word. -/
theorem Request.field_lengths_le {modular : Bool} (r : Request modular) :
    (frame (callWord r.header.call)).length≤r.word.length ∧
    (frame ((Header.baseHeaderValues r.header).flatMap natWord)).length≤r.word.length ∧
    r.countsWord.length≤r.word.length ∧ r.geometryField.length≤r.word.length ∧
    (termsWord r.terms).length≤r.word.length ∧ (natWord r.scale).length≤r.word.length := by
  simp only [Request.word,Request.contextWord,Request.geometryField,Top.loadRec,
    List.length_append,frame_length]
  omega

/-- `lem:print`, paper/paper.tex: the source
reader and the complete arithmetic share one actual fixed word bound. -/
structure InputFits {modular : Bool} (C : Ctx) (r : Request modular) extends Fits C r where
  arityRead : natBitLength r.header.call.n+2≤C.Wd
  indexRead : natBitLength r.walkCode.val+2≤C.Wd
  degreeRead : natBitLength r.degree+2≤C.Wd
  scaleRead : natBitLength r.scale+2≤C.Wd
  scaleField : (natWord r.scale).length<2^C.Wd
  geometry : r.geometryField.length<2^C.Wd
  headerArithmetic : 4*(r.header.call.n+1)^2+r.header.call.n+20<2^C.Wd
  packingArithmetic :
    (r.degree+2)*(r.toRowContext.nativeFieldWidth+2*((r.header.call.n+1)/2)+r.degree+4)+
      r.coefficientBits+r.header.call.n+r.toRowContext.nativeFieldWidth+r.degree+30<2^C.Wd

/-- `lem:print`, paper/paper.tex: the measured
finite word and original metadata imply every reader and writer guard;
no field height, row width or source length is supplied at runtime. -/
theorem inputFits_of_sizing {modular : Bool} (C : Ctx) (r : Request modular)
    (hW : r.sizingMagnitude+10≤C.Wd) : InputFits C r := by
  have hpow : C.Wd<2^C.Wd:=Nat.lt_two_pow_self
  have hmag:=hW
  unfold Request.sizingMagnitude at hmag
  dsimp only at hmag
  have hlen : r.word.length<2^C.Wd :=
    (lt_natBitLength r.word.length).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hl:=r.field_lengths_le
  have hbits (v : ℕ) : natBitLength v≤v+1 := by
    unfold natBitLength
    have hh:=Nat.log_le_self 2 v
    omega
  have hwidth : r.termRequest.stackWidth≤
      (r.degree+2)*(r.toRowContext.nativeFieldWidth+2*((r.header.call.n+1)/2)+r.degree+4)+
      r.coefficientBits+4 := by
    rw [r.stackWidth_actual]
    unfold NativeWidth.packedBits
    omega
  have hn:=hbits r.header.call.n
  have hd:=hbits r.degree
  have hw:=hbits r.termRequest.stackWidth
  refine ⟨⟨hl.1.trans_lt hlen, hl.2.1.trans_lt hlen,
    hl.2.2.1.trans_lt hlen, hl.2.2.2.2.1.trans_lt hlen,
    by omega, by omega, by omega, by omega⟩,
    by omega, by omega, by omega, by omega,
    hl.2.2.2.2.2.trans_lt hlen, hl.2.2.2.1.trans_lt hlen, by omega, by omega⟩

end NearQuarticWires.StagePrint.EntryFormat
