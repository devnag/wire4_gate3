import Proof.Quartic.StagePrint.EntryEmitReady
import Proof.Quartic.StagePrintContext.GeometryField

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the output
has the exact existing eleven-field Tuple input order. -/
def writerProgram : St VV MM :=
  .seq (emitStoredField 0 callLengthVar)
  (.seq (emitStoredField 1 baseLengthVar)
  (.seq contextFieldProgram
  (.seq (emitStoredField 7 termsLengthVar)
  (.seq (emitFramedVariable GreedyEntry.widthVar)
  (.seq (emitFramedVariable GreedyEntry.degreeVar)
    (StagePrintContext.emitLiteral (List.replicate 5 false)))))))

/-- `prop:time`, paper/paper.tex: output
formatting is linear in the retained source and Terms bits, plus
binary scalar lengths, independently of following walk entries. -/
noncomputable def writerSteps {modular : Bool} (r : Request modular) : ℕ :=
  11*((frame (callWord r.header.call)).length+
    (frame ((Header.baseHeaderValues r.header).flatMap natWord)).length+
    (termsWord r.terms).length)+27*r.countsWord.length+
    120*(natBitLength r.walkCode.val+natBitLength r.termRequest.stackWidth+
      natBitLength r.degree)+452

/-- `lem:print`, paper/paper.tex: the fourth
Tuple field is the same retained three counts followed by the actual
walk ordinal, in the original literal natural-codec order. -/
theorem Request.tuple_context_word {modular : Bool} (r : Request modular) :
    r.termRequest.contextWord=r.countsWord++natWord r.walkCode.val := by
  simp only [StageTuple.TermCutRequest.contextWord,Request.termRequest,
    StageNativeWidth.termCutRequest,Request.countsWord,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.append_assoc]

/-- `lem:print`, paper/paper.tex: the complete
physical writer constructs the actual eleven-field Tuple request
from retained real bytes, measured lengths and computed widths. -/
theorem writerProgram_run {modular : Bool} (C : Ctx) (r : Request modular)
    (a : DS VV MM) (ha : Ready r a) (hfit : Fits C r) :
    Hs C writerProgram a (writerSteps r) (fun z=>z.out=a.out++r.termRequest.word) := by
  unfold writerProgram
  refine Hx.hs (Hs.then (storedField_ready C r 0 callLengthVar (by decide)
    (frame (callWord r.header.call)) a ha ha.1.callBits ha.1.callLength hfit.call) ?_)
  rintro b ⟨bo,bReady⟩ n1 hn1
  refine Hs.then (storedField_ready C r 1 baseLengthVar (by decide)
    (frame ((Header.baseHeaderValues r.header).flatMap natWord)) b bReady
      bReady.1.baseBits bReady.1.baseLength hfit.base) ?_
  rintro d ⟨do_,dReady⟩ n2 hn2
  refine Hs.then (contextField_ready C r d dReady hfit) ?_
  rintro e ⟨eo,eReady⟩ n3 hn3
  refine Hs.then (storedField_ready C r 7 termsLengthVar (by decide)
    (termsWord r.terms) e eReady eReady.1.termBits eReady.1.termLength hfit.terms) ?_
  rintro f ⟨fo,fReady⟩ n4 hn4
  refine Hs.then (framedScalar_ready C r GreedyEntry.widthVar (by decide)
    r.termRequest.stackWidth f fReady fReady.1.width hfit.wordWidth hfit.width) ?_
  rintro g ⟨go,gReady⟩ n5 hn5
  refine Hs.then (framedScalar_ready C r GreedyEntry.degreeVar (by decide)
    r.degree g gReady gReady.1.degree hfit.wordWidth hfit.degree) ?_
  rintro h ⟨ho,_hReady⟩ n6 hn6
  refine Hs.last (StagePrintContext.emitLiteral_run C (List.replicate 5 false) h) ?_
  rintro z zo n7 hn7
  refine ⟨?_,?_⟩
  · rw [zo,ho,go,fo,eo,do_,bo]
    unfold StageTuple.TermCutRequest.word
    rw [r.tuple_context_word]
    simp only [Request.termRequest,StageNativeWidth.termCutRequest,Top.loadRec,
      List.append_assoc]
    rfl
  · change n7≤2*5+1 at hn7
    unfold writerSteps
    omega

end NearQuarticWires.StagePrint.EntryFormat
