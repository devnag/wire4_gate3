import Proof.Quartic.StageCarrierEnvelope.MetadataCost
import Proof.Gates.CounterMachine.TabCallDock
import Proof.Gates.Expand.PolyTabPack
import Proof.Gates.Codec.Unframe

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Codec
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: the single
metadata call has a disjoint physical bank outside both source tapes. -/
def bankMap (t : ℕ) (j : Fin t) : Fin (t+4) := ⟨j.val+2,by omega⟩

def bankRuler (t : ℕ) : Fin (t+4) := ⟨t+2,by omega⟩

def bankOut (t : ℕ) : Fin (t+4) := ⟨t+3,by omega⟩

theorem bankMap_injective (t : ℕ) : Function.Injective (bankMap t) := by
  intro i j h
  apply Fin.ext
  have hh:=congrArg Fin.val h
  dsimp [bankMap] at hh
  omega

theorem bankMap_ne_ruler (t : ℕ) (j : Fin t) : bankMap t j≠bankRuler t := by
  intro h
  have hh:=congrArg Fin.val h
  dsimp [bankMap,bankRuler] at hh
  omega

theorem bankMap_off (t : ℕ) (j : Fin t) :
    bankMap t j≠(0 : Fin (t+4)) ∧ bankMap t j≠1 ∧ bankMap t j≠bankOut t := by
  refine ⟨?_,?_,?_⟩ <;> intro h <;> have hh:=congrArg Fin.val h <;>
    simp only [bankMap,bankOut,Fin.val_zero,Fin.val_one] at hh <;> omega

/-- `lem:print`, paper/paper.tex: only the
actual once-call ruler is nonempty blank workspace at the cold entry. -/
def bankLens (t budget : ℕ) (i : Fin (t+4)) : ℕ := if i.val=t+2 then budget else 0

/-- `lem:print`, paper/paper.tex: the original
finite source is copied once to the actual ordinary metadata callee. -/
noncomputable def metadataBank (B1 B2 : ℕ) :
    WMX ((metadataWordFunction B1 B2).program.tapeCount+3) 16 :=
  let f:=metadataWordFunction B1 B2
  .seq (.wm (copyRW 0 (bankMap f.program.tapeCount (tape0 f.program)) 10 11 12))
    (.machZ f.program.machine (bankMap f.program.tapeCount) (bankRuler f.program.tapeCount))

/-- `lem:print`, paper/paper.tex: the one
real metadata reply is docked with its original source preserved and
both raw-source and final-output tapes still physically empty. -/
structure BankReady {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (a : WState ((metadataWordFunction B1 B2).program.tapeCount+3) 16) : Prop where
  source : a.st 0=frame (StagePrint.TermsCarrier.word r)
  sourceHead : a.sh 0=0
  raw : a.st 1=[]
  rawHead : a.sh 1=0
  output : a.st (bankOut (metadataWordFunction B1 B2).program.tapeCount)=[]
  outputHead : a.sh (bankOut (metadataWordFunction B1 B2).program.tapeCount)=0
  column : a.st (bankMap (metadataWordFunction B1 B2).program.tapeCount
    (metadataWordFunction B1 B2).program.outputTape)=frame (NearCubicWires.RepairRepresentation.natWord r.child.cellCall.ncol)
  columnHead : a.sh (bankMap (metadataWordFunction B1 B2).program.tapeCount
    (metadataWordFunction B1 B2).program.outputTape)=0
  regs : ∀i,a.val i=0

/-- `lem:print` and `prop:time`, paper/paper.tex: one actual cold call, its finite input copy and its
real reset ruler are charged before any envelope field is written. -/
theorem metadataBank_run {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) (cap : ℕ)
    (hc : 4*(StagePrint.TermsCarrier.word r).length+4≤cap) :
    ∃ b, WXExec cap (metadataBank B1 B2)
      (idealStart ((metadataWordFunction B1 B2).program.tapeCount+3) 16
        (StagePrint.TermsCarrier.word r) (bankLens (metadataWordFunction B1 B2).program.tapeCount (metadataBudget r)))
      b (2*metadataBudget r+200*((StagePrint.TermsCarrier.word r).length+1)) ∧ BankReady r b := by
  let f:=metadataWordFunction B1 B2
  let t:=f.program.tapeCount
  have ht : 2≤t:=f.program.twoTapes
  let a:=idealStart (t+3) 16 (StagePrint.TermsCarrier.word r) (bankLens t (metadataBudget r))
  have ec:=copyRW_spec cap (0 : Fin (t+4)) (bankMap t (tape0 f.program))
    ((bankMap_off t (tape0 f.program)).1.symm) (10 : Fin 16) 11 12
    (by decide) (by decide) (by decide) (StagePrint.TermsCarrier.word r) [] a
    (by simp [a,idealStart]) rfl
    (by simp [a,idealStart,bankLens,bankMap,tape0];omega) rfl rfl rfl rfl hc
  let a1:=a.sets (bankMap t (tape0 f.program)) (frame (StagePrint.TermsCarrier.word r))
  have hblank : ∀j,j≠tape0 f.program→a1.st (bankMap t j)=[] := by
    intro j hj
    have hne:=fun h=>hj (bankMap_injective t h)
    simp only [a1,WState.sets_st,Function.update_of_ne hne]
    simp [a,idealStart,bankLens,bankMap]
    omega
  have hruler : a1.st (bankRuler t)=List.replicate (metadataBudget r) false := by
    have hne:=(bankMap_ne_ruler t (tape0 f.program)).symm
    simp only [a1,WState.sets_st,Function.update_of_ne hne]
    simp [a,idealStart,bankRuler,bankLens]
  obtain ⟨b,eb,hcol,hheads,hoff,hregs⟩:=wfDock_exact f r cap (bankMap t) (bankMap_injective t)
    (bankRuler t) (bankMap_ne_ruler t) a1 (by simp [a1]) hblank (fun _=>rfl)
    (metadataBudget r) hruler rfl le_rfl
  have h0:=hoff 0 (fun j=>(bankMap_off t j).1)
  have h1:=hoff 1 (fun j=>(bankMap_off t j).2.1)
  have ho:=hoff (bankOut t) (fun j=>(bankMap_off t j).2.2)
  refine ⟨b,(WXExec.seq (WXExec.wm ec) eb).mono (by omega),?_⟩
  constructor
  · rw [h0.1];simp [a1,a,idealStart,(bankMap_off t (tape0 f.program)).1.symm]
  · exact h0.2
  · rw [h1.1];simp [a1,a,idealStart,bankLens,bankMap,tape0]
  · exact h1.2
  · rw [ho.1];simp [a1,a,idealStart,bankLens,bankOut,bankMap,tape0]
  · exact ho.2
  · exact hcol
  · exact hheads f.program.outputTape
  · intro i;rw [hregs];rfl

end NearQuarticWires.StageCarrierEnvelope
