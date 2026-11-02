import Proof.Quartic.StagePrint.EntryInputFits
import Proof.Quartic.StagePrint.EntryCoefficientBits
import Proof.Quartic.StagePrint.EntryWidthComplete

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat
open NearCubicWires NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the three
physical arithmetic stages compute source width, coefficient bits and
packing width while preserving all real retained finite fields. -/
def computeWidths (modular : Bool) : St VV MM :=
  .seq Header.headerWidthProgram
    (.seq (GreedyEntry.coefficientBitsProgram modular) GreedyEntry.packingWidthProgram)

def computeScratch : List (Fin VV) :=
  [aw0,Header.sizeVar,Header.work,Header.Lin,Header.Lout,StageFormulaMetadata.fieldBytesVar,
    GreedyEntry.coefficientBitsVar,vJ,GreedyEntry.halfVar,GreedyEntry.sumVar,
    GreedyEntry.factorVar,GreedyEntry.productVar,GreedyEntry.widthVar]

/-- `lem:print`, paper/paper.tex: metadata
read from the actual source determines the exact existing native
Tuple width, with no supplied decoded width or stream length. -/
theorem computeWidths_run {modular : Bool} (C : Ctx) (r : Request modular)
    (a : DS VV MM) (hc : Cst a)
    (hn : a.env Header.arity=r.header.call.n)
    (hd : a.env GreedyEntry.degreeVar=r.degree)
    (hs : a.env GreedyEntry.modulusVar=r.scale) (hfit : InputFits C r) :
    Hs C (computeWidths modular) a
      (5*Nat.size r.header.call.n+5*natBitLength r.scale+181)
      (fun z=>z.env GreedyEntry.widthVar=r.termRequest.stackWidth ∧ z.sh=a.sh ∧
        Cst z ∧ Fr a z computeScratch) := by
  unfold computeWidths
  have eh:=Header.headerWidthProgram_run C a hc r.header.call.n hn hfit.headerArithmetic
  refine (Hs.seq (t2:=5*natBitLength r.scale+71) eh
    fun b ⟨_blin,bl,bsh,bc,bfr⟩=>?_).mono (by omega) (fun _ h=>h)
  have bL : b.env Header.Lout=r.toRowContext.nativeFieldWidth := by
    simpa only [StageTuple.RowContext.nativeFieldWidth,StageTuple.RowContext.inputFieldWidth] using bl
  have bn : b.env Header.arity=r.header.call.n := by rw [bfr _ (by decide),hn]
  have bd : b.env GreedyEntry.degreeVar=r.degree := by rw [bfr _ (by decide),hd]
  have bs : b.env GreedyEntry.modulusVar=r.scale := by rw [bfr _ (by decide),hs]
  refine Hs.seq (t2:=40) (GreedyEntry.coefficientBitsProgram_run C modular r.scale b bc bs hfit.scaleField)
    fun d ⟨dbits,dsh,dc,dfr⟩=>?_
  have dn : d.env Header.arity=r.header.call.n := by rw [dfr _ (by decide),bn]
  have dL : d.env Header.Lout=r.toRowContext.nativeFieldWidth := by rw [dfr _ (by decide),bL]
  have dd : d.env GreedyEntry.degreeVar=r.degree := by rw [dfr _ (by decide),bd]
  have dcb : d.env GreedyEntry.coefficientBitsVar=r.coefficientBits := dbits
  refine (GreedyEntry.packingWidthProgram_run C d dc r.header.call.n r.toRowContext.nativeFieldWidth
    r.degree r.coefficientBits dn dL dd dcb hfit.packingArithmetic).mono le_rfl ?_
  rintro z ⟨zw,zsh,zc,zfr⟩
  refine ⟨zw.trans r.stackWidth_actual.symm,zsh.trans (dsh.trans bsh),zc,?_⟩
  exact (bfr.weaken (by simp [computeScratch])).trans
    ((dfr.weaken (by simp [computeScratch])).trans (zfr.weaken (by simp [computeScratch])))

end NearQuarticWires.StagePrint.EntryFormat
