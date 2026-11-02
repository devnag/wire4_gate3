import Proof.Quartic.StageCertNative.CopyFrame
import Proof.Quartic.StageRecovery.FieldSequence
import Proof.Quartic.StagePrint.EntryMemory

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells

def equalityDimension : Fin VV:=90

/-- `imp:partition` and `lem:print`, paper/paper.tex: the canonical native coordinate width is
computed from original n by increment and integer halving. -/
def computeEqualityDimension : St VV MM :=
  .seq (.op (.copy equalityDimension StagePrint.Header.arity))
    (.seq (.op (.inc equalityDimension)) (.op (.half equalityDimension)))

theorem computeEqualityDimension_run (C : Ctx) (n : ℕ) (a : DS VV MM) (hc : Cst a)
    (hn : a.env StagePrint.Header.arity=n) (hfit : n+1<2^C.Wd) :
    Hs C computeEqualityDimension a 5 (fun z=>
      z.env equalityDimension=(n+1)/2 ∧ z.sh=a.sh ∧ Cst z ∧ Fr a z [equalityDimension]) := by
  unfold computeEqualityDimension
  refine Hx.hs (Hs.then (hs_copy C equalityDimension StagePrint.Header.arity a (by decide)) ?_)
  rintro b rfl n0 hn0
  refine Hs.then (hs_inc C equalityDimension _ (by simpa only [DS.set_env_self,hn] using hfit)) ?_
  rintro d rfl n1 hn1
  refine Hs.last (hs_half C equalityDimension _) ?_
  rintro z rfl n2 hn2
  have hf : Fr a (((a.set equalityDimension (a.env StagePrint.Header.arity)).set
      equalityDimension ((a.env StagePrint.Header.arity)+1)).set equalityDimension
        ((a.env StagePrint.Header.arity+1)/2)) [equalityDimension] :=
    (Fr.set a _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))
  refine ⟨⟨?_,rfl,Cst.of_fr hc hf (by decide),hf⟩,by omega⟩
  simp only [DS.set_env_self,hn]

/-- `lem:print`, paper/paper.tex: the exact
raw equality stream is copied by its frame markers, followed by two
actually generated unary dimensions and the eight literal empty fields. -/
def emitEqualityFields : St VV MM :=
  .seq copyRawFrame (.seq (StageRecovery.FixedBits.emitUnaryFrom equalityDimension)
    (.seq (StageRecovery.FixedBits.emitUnaryFrom StagePrint.GreedyEntry.widthVar)
      (StageLift.emitLiteral [false,false,false,false,false,false,false,false])))

theorem emitEqualityFields_run (C : Ctx) (raw : List Bool) (width fieldWidth : ℕ)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip=frame raw)
    (hw : a.env equalityDimension=width)
    (hf : a.env StagePrint.GreedyEntry.widthVar=fieldWidth)
    (hwidth : width<2^C.Wd) (hfield : fieldWidth<2^C.Wd) :
    Hs C emitEqualityFields a (11*raw.length+9*width+9*fieldWidth+50) (fun z=>
      z.out=a.out++Top.loadRec raw (List.replicate width true)
        (List.replicate fieldWidth true) [] [] [] [] [] [] [] []) := by
  unfold emitEqualityFields
  refine Hx.hs (Hs.then (copyRawFrame_run C raw [] a hc
    (by simpa only [List.append_nil] using hin)) ?_)
  rintro b ⟨_bi,bo,_bs,bc,bfr⟩ n0 hn0
  have bw : b.env equalityDimension=width := (bfr _ (by decide)).trans hw
  have bf : b.env StagePrint.GreedyEntry.widthVar=fieldWidth := (bfr _ (by decide)).trans hf
  refine Hs.then (StageRecovery.FixedBits.emitUnaryFrom_spec C b bc equalityDimension
    (by decide) (by decide) width bw hwidth) ?_
  rintro d ⟨doo,_ds,dc,dfr⟩ n1 hn1
  have df : d.env StagePrint.GreedyEntry.widthVar=fieldWidth := (dfr _ (by decide)).trans bf
  refine Hs.then (StageRecovery.FixedBits.emitUnaryFrom_spec C d dc StagePrint.GreedyEntry.widthVar
    (by decide) (by decide) fieldWidth df hfield) ?_
  rintro e ⟨eo,_es,ec,_efr⟩ n2 hn2
  refine Hs.last (StageLift.emitLiteral_spec C [false,false,false,false,false,false,false,false] e ec) ?_
  rintro z ⟨zo,_zs,_zc,_zf⟩ n3 hn3
  change n3≤17 at hn3
  refine ⟨?_,by omega⟩
  rw [zo,eo,doo,bo]
  simp only [Top.loadRec,frame,List.append_assoc]
  rfl

end NearQuarticWires.StageCertNative
