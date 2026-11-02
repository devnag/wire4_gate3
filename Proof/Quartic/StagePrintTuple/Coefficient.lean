import Proof.Quartic.StagePrint.RawSigned
import Proof.Quartic.StagePrint.RawSourceBounds
import Proof.Quartic.StagePrint.RawConstants

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms.SInt (encS)
open StagePrint.RawBits

/-- `lem:print`, paper/paper.tex: one signed
monomial coefficient and its actual fixed field width form an isolated
finite conversion packet, rather than the complete Terms source. -/
structure CoefficientRequest where
  width : ℕ
  coefficient : ℤ

/-- `lem:print`, paper/paper.tex: the width and
canonical signed coefficient are both actual serialized input fields. -/
def CoefficientRequest.word (r : CoefficientRequest) : List Bool :=
  natWord r.width ++ intWord r.coefficient

/-- `lem:print`, paper/paper.tex: the coefficient
formatter returns the exact fixed signed field with its two literal
native-load framing layers, preserving negative and zero coefficients. -/
def CoefficientRequest.output (r : CoefficientRequest) : List Bool :=
  frame (frame (SignedSortKey.binary r.width (encS r.coefficient)))

/-- `lem:print`, paper/paper.tex: binary source
arithmetic parses the coefficient once and emits its fixed signed field;
its register width depends only on this isolated finite source packet. -/
def coefficientProgram : St VV :=
  .seq initializeConstants (.seq readNat (.seq (.op (.copy width t3))
    (.seq (readSignedField 2) (emitL [true, false, false]))))

/-- `prop:time`, paper/paper.tex: the isolated
coefficient conversion pays input parsing, fixed-width bit emission and
all initialization and framing work. -/
def CoefficientRequest.steps (r : CoefficientRequest) : ℕ :=
  30 * natBitLength r.width + 60 * (intWord r.coefficient).length + 30 * r.width + 200

/-- `lem:print`, paper/paper.tex: the actual
binary coefficient converter starts cold and produces exactly its
native fixed-field bytes, without unary iteration through its magnitude. -/
theorem coefficientProgram_run (C : Ctx) (r : CoefficientRequest)
    (hcw : C.cw = r.word) (hW : C.cw.length + 3 ≤ C.Wd) :
    Hs C coefficientProgram (a0 (V := VV)) r.steps (fun b => b.out = r.output) := by
  have hctx : 3 ≤ C.Wd := by omega
  have hlen : C.cw.length + 2 < 2 ^ C.Wd :=
    lt_of_lt_of_le (by omega : C.cw.length + 2 < C.Wd) (Nat.lt_two_pow_self.le)
  have hbits : natBitLength r.width ≤ C.cw.length := by
    have hb := natBitLength_le_len r.width
    rw [hcw, CoefficientRequest.word, List.length_append]
    omega
  have hwidth : r.width < 2 ^ C.Wd :=
    (lt_natBitLength r.width).trans_le (Nat.pow_le_pow_right (by decide) (hbits.trans (by omega)))
  have hcoeff : encS r.coefficient < 2 ^ C.Wd := by
    have hz : (intWord r.coefficient).length ≤ C.cw.length := by
      rw [hcw, CoefficientRequest.word, List.length_append]
      omega
    have hh := signed_code_word_bound r.coefficient C.cw.length hz
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hW
    omega
  unfold coefficientProgram
  refine Hx.hs (Hs.then (initialize_run C hctx) (fun a ⟨ac, ap, _, ao, _⟩ n1 hn1 => ?_))
  have hd : C.cw.drop a.cp = natWord r.width ++ intWord r.coefficient := by
    rw [ap, List.drop_zero, hcw]
    rfl
  refine Hs.then (readNat_spec a ac r.width _ hd (by omega) hlen)
    (fun b ⟨bv, _, bp, _, bo, bc, _⟩ n2 hn2 => ?_)
  refine Hs.then (hs_copy C width t3 b (by decide)) (fun e he n3 hn3 => ?_)
  subst he
  let e := b.set width (b.env t3)
  have ef : Fr b e [width] := Fr.set _ _ (by simp)
  have ec : Cst e := Cst.of_fr bc ef (by decide)
    (by rw [ef vPOS (by decide)]; exact bc.pos)
  have ed : C.cw.drop e.cp = intWord r.coefficient ++ [] := by
    change C.cw.drop b.cp = _
    rw [bp, ← List.drop_drop, hd, List.drop_left, List.append_nil]
  have ew : e.env width = r.width := by simp [e, bv]
  refine Hs.then (readSignedField_run C 2 e ec r.coefficient [] r.width ed ew hcoeff hwidth
    hctx (by omega) hlen) (fun f ⟨fo, _, _, _, fc, _⟩ n4 hn4 => ?_)
  refine Hs.last (emitL_spec (C := C) [true, false, false] f) (fun g ⟨go, _, _, _⟩ n5 hn5 => ?_)
  refine ⟨?_, ?_⟩
  · rw [go, fo, layered_two_eq]
    simp [CoefficientRequest.output, e, bo, ao, frame_eq_frameP, frameP,
      List.flatMap_append, List.append_assoc]
  · unfold CoefficientRequest.steps
    norm_num at hn5
    omega

end NearQuarticWires.StageTuple
