import Proof.Quartic.StageNativeKidsPool.ColdLayout
import Proof.Quartic.Control.Frame

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control StageTuple StageNativeKids

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: an
actual ordinary call with a private reset ruler avoids every external
stream outside its mapped ordinary bank and ruler. -/
theorem machZ_avoids {t s : ℕ} (M : Machine t s) (bank : Fin t→Fin (ns+1))
    (ruler final : Fin (ns+1)) (hb:∀j,bank j≠final) (hr:ruler≠final) :
    WMX.Avoids final (WMX.machZ (nr:=nr) M bank ruler) := by
  simp only [WMX.machZ,WMX.Avoids]
  intro j
  refine Fin.addCases (fun i=>?_) (fun _ : Fin 1=>?_) j
  · simpa only [Fin.addCases_left] using hb i
  · simpa only [Fin.addCases_right] using hr

/-- `lem:print`, paper/paper.tex: copying
and clearing a real row call affects only its actual bank, guard,
tally, ruler and chosen raw-output stream. -/
theorem callRecords_avoids {p : Program} (s : Site p ns nr) (out final : Fin (ns+1))
    (OP : Fin nr) (hb:∀j,s.bank j≠final) (ht:s.tally≠final)
    (hg:s.guard≠final) (hr:s.ruler≠final) (ho:out≠final) :
    WMX.Avoids final (callRecordsProgram s out OP) := by
  have hs : ∀j,s.swept j≠final:=by
    intro j
    refine Fin.addCases (fun i=>?_) (fun _ : Fin 1=>?_) j
    · simpa only [Site.swept,Fin.addCases_left] using hb i
    · simpa only [Site.swept,Fin.addCases_right] using ht
  have hsG : ∀j,(Fin.addCases (motive:=fun _=>Fin (ns+1)) s.swept (fun _ : Fin 1=>s.guard)) j≠final:=by
    intro j
    refine Fin.addCases (fun i=>?_) (fun _ : Fin 1=>?_) j
    · simpa only [Fin.addCases_left] using hs i
    · simpa only [Fin.addCases_right] using hg
  have hc : WMX.Avoids final (callP s):=by
    unfold callP
    refine ⟨?_,?_,?_⟩
    · simp [WMX.Avoids,WM.Avoids,WorkerArith.guardP,WorkerArith.twoOnes,Site.input,hb,hg,
        BinW.width,BinW.widthW,BinW.widthLoop,BinW.backLoop,WM.rewind,
        WMX.wr,WMX.fwd,WMX.bwd,WMX.inc,WMX.dec,WMX.skip]
    · exact machZ_avoids _ _ _ _ hs hr
    · simp [WMX.Avoids,WM.Avoids,WorkerArith.tallyP,WM.rewind,ht,hg,
        WMX.wr,WMX.fwd,WMX.bwd,WMX.inc,WMX.dec,WMX.skip]
  have hclean : WMX.Avoids final (cleanP s):=by
    unfold cleanP eraseP
    refine ⟨machZ_avoids _ _ _ _ hsG hr,?_⟩
    simp [WMX.Avoids,WM.Avoids,WorkerArith.clearSelfP,hg,WM.clear,WM.move,
      WMX.wr,WMX.fwd,WMX.bwd,WMX.inc,WMX.dec,WMX.skip]
  refine ⟨hc,?_,hclean⟩
  simp [WMX.Avoids,WM.Avoids,appendRecordsReset,CounterAsm.frameLoop,CounterAsm.frameCopy,
    NearCubicGates.Close.Recovery.HTParts.pairLoop,NearCubicGates.Close.Recovery.HTParts.cellE,
    emitC,WM.fwdC,WM.rewind,hb,ho]

/-- `lem:print`, paper/paper.tex: the
source/header/index formatter leaves every external fresh output stream
untouched while constructing its actual nested row-call input. -/
theorem counterInput_avoids (P : Fin 3 ↪ Fin (ns+1)) (R : Fin 5 ↪ Fin nr)
    (final : Fin (ns+1)) (hp:∀i,P i≠final) :
    WM.Avoids final (pipelineCounterInputProgram P R) := by
  simp [WM.Avoids,pipelineCounterInputProgram,appendNestedFieldReset,emitDoublePair,
    CounterAsm.frameCopy,NearCubicGates.Close.Recovery.HTParts.pairLoop,
    NearCubicGates.Close.Recovery.HTParts.cellE,copyNestedIndex,emitNestedUnary,repeatLiteral,
    NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR,
    NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup,WM.clear,WM.move,
    emitWordM,emitPair,emitC,WM.fwdC,WM.rewind,hp]

/-- `lem:print`, paper/paper.tex: the
complete counted raw-row loop leaves the fresh final framed output
tape exactly untouched, including its literal blank tail and head. -/
theorem loop_avoids_final (counter row : Program) :
    WMX.Avoids (⟨15,by unfold streams;omega⟩ : Fin (streams counter row+1))
      (loopProgram (rowLayout counter row)) := by
  let final : Fin (streams counter row+1):=⟨15,by unfold streams;omega⟩
  have hb : ∀j,(rowSite counter row).bank j≠final:=by
    intro j h;have hv:=congrArg Fin.val h;change 20+counter.tapeCount+j.val=15 at hv;omega
  have hp : ∀i,rowSources counter row i≠final:=by
    intro i h
    have hv:=congrArg Fin.val h
    fin_cases i <;> simp [rowSources,rowSite,Site.input,rowMap,WorkerArith.inTape,final] at hv
    all_goals omega
  have hc:=callRecords_avoids (rowSite counter row) (⟨14,by unfold streams;omega⟩) final
    (10 : Fin 16) hb
    (by intro h;have hv:=congrArg Fin.val h;change 17=15 at hv;omega)
    (by intro h;have hv:=congrArg Fin.val h;change 18=15 at hv;omega)
    (by intro h;have hv:=congrArg Fin.val h;change 19=15 at hv;omega)
    (by intro h;have hv:=congrArg Fin.val h;change 14=15 at hv;omega)
  change WMX.Avoids final _
  simp only [loopProgram,WMX.Avoids,WMX.dec,WM.Avoids,occurrenceProgram,WMX.inc]
  exact ⟨trivial,counterInput_avoids _ _ _ hp,hc,trivial⟩

end NearQuarticWires.StageNativeKidsPool
