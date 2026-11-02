import Proof.Quartic.StagePrint.RawWeightEncoding

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `lem:print`, paper/paper.tex: a ready constant field is emitted with the original child loader's two framing layers. -/
def emitFixedField : St VV := .seq (emitBinary 2) (emitL [true,false,false])

/-- `lem:print` and `prop:time`, paper/paper.tex: constant fields are physically written in time linear in the common word width. -/
theorem emitFixedField_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (v W : ℕ) (hv : a.env value=v) (hw : a.env width=W)
    (hW : W<2^C.Wd) (hctx : 3≤C.Wd) :
    Hs C emitFixedField a (30*W+12) (fun b=>
      b.out=a.out++frame (frame (binary W v)) ∧ b.cp=a.cp ∧ b.wq=a.wq ∧
      b.env width=W ∧ Cst b ∧ Fr a b scratch) := by
  unfold emitFixedField
  refine Hs.mono (Hs.seq (t2:=7) (emitBinary_run C 2 a hc v W hv hw hW hctx)
    (fun b ⟨_,_,bw,bo,bp,bq,bc,bf⟩=>?_)) (by norm_num;omega) (fun _ h=>h)
  refine (emitL_spec (C:=C) [true,false,false] b).mono le_rfl ?_
  rintro e ⟨eo,ep,ew,ef⟩
  have ec : Cst e:=Cst.of_fr bc ef (by decide)
    (by rw [ef vPOS (by decide),bc.pos,ep])
  refine ⟨?_,ep.trans bp,ew.trans bq,?_,ec,bf.trans (ef.weaken (by decide))⟩
  · rw [eo,bo,layered_two_eq]
    simp [frame_eq_frameP,frameP,List.flatMap_append,List.append_assoc]
  · rw [ef width (by decide)];exact bw

/-- `lem:print`, paper/paper.tex: the original compiler's fixed zero and two fields have no input-dependent constructor. -/
def emitConstantField (v : ℕ) : St VV := .seq (setK value v) emitFixedField

/-- `lem:print`, paper/paper.tex: every constant field begins with actual register initialization. -/
theorem emitConstantField_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (v W : ℕ) (hw : a.env width=W) (hv : v<2^C.Wd)
    (hW : W<2^C.Wd) (hctx : 3≤C.Wd) :
    Hs C (emitConstantField v) a (30*W+2*v+16) (fun b=>
      b.out=a.out++frame (frame (binary W v)) ∧ b.cp=a.cp ∧ b.wq=a.wq ∧
      b.env width=W ∧ Cst b ∧ Fr a b scratch) := by
  unfold emitConstantField
  refine Hs.mono (Hs.seq (t2:=30*W+12) (setK_spec value (by decide) v a hv)
    (fun b ⟨bv,bp,bq,bo,bf⟩=>?_)) (by omega) (fun _ h=>h)
  have bc : Cst b:=Cst.of_fr hc bf (by decide)
    (by rw [bf vPOS (by decide),hc.pos,bp])
  refine (emitFixedField_run C b bc v W bv
    (by rw [bf width (by decide)];exact hw) hW hctx).mono le_rfl ?_
  rintro e ⟨eo,ep,eq,ew,ec,ef⟩
  exact ⟨by rw [eo,bo],ep.trans bp,eq.trans bq,ew,ec,
    (bf.weaken (by decide)).trans ef⟩

end NearQuarticWires.StagePrint.RawBits
