import Proof.Gates.Expand.PolyTabStage2b
import Proof.Gates.Expand.Machine

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Expand NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Tabulator
open NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.FinalPass.Tm

noncomputable abbrev expandTapes (E : ExpandMachine) : ℕ := E.wf.program.tapeCount

def expandMap (E : ExpandMachine) (j : Fin (expandTapes E)) : Fin (expandTapes E+2) :=
  ⟨j.val,by omega⟩

noncomputable def expandSource (E : ExpandMachine) : Fin (expandTapes E+2) :=
  expandMap E E.wf.program.outputTape

noncomputable def expandOutput (E : ExpandMachine) : Fin (expandTapes E+2) :=
  ⟨expandTapes E,by omega⟩

noncomputable def expandRuler (E : ExpandMachine) : Fin (expandTapes E+2) :=
  ⟨expandTapes E+1,by omega⟩

def expandRegisters : Fin 8 ↪ Fin 9 :=
  ⟨fun i=>⟨i.val,by omega⟩,fun i j h=>Fin.ext (congrArg (fun z : Fin 9=>z.val) h)⟩

theorem expandRegisters_ne (i : Fin 8) : expandRegisters i≠(8 : Fin 9) := by
  intro h
  have hh:=congrArg Fin.val h
  have:=i.isLt
  change i.val=8 at hh
  omega

/-- `lem:print`, paper/paper.tex: the actual
expansion machine's raw Terms output is followed by the counted
list/support/signed-integer codec copier and one outer delimiter. -/
noncomputable def expandFrameProgram (E : ExpandMachine) : WMX (expandTapes E+1) 9 :=
  .seq (.machZ E.wf.program.machine (expandMap E) (expandRuler E))
    (cpTerms (expandSource E) (expandOutput E) expandRegisters 8 expandRegisters_ne)

noncomputable def expandFrameLens (E : ExpandMachine) (r : FormulaReq)
    (i : Fin (expandTapes E+2)) : ℕ := if i=expandRuler E then E.budget r else 0

noncomputable def expandFrameSteps (E : ExpandMachine) (r : FormulaReq) : ℕ :=
  2*E.budget r+cpTermsCost (E.expand r)+3

noncomputable def expandFrameCapacity (E : ExpandMachine) (r : FormulaReq) : ℕ :=
  let P:=E.expand r
  2^(natBitLength r.1+1)+r.1+2^(natBitLength P.length+1)+P.length+
    6*natBitLength r.1+6*natBitLength P.length+2*(termsWord P).length+20

/-- `lem:print` and `prop:time`, paper/paper.tex: framing reads the actual monomial and support counts;
it has no output-length oracle and retains every signed coefficient. -/
theorem expandFrameProgram_run (E : ExpandMachine) (r : FormulaReq) :
    Runs (expandFrameCapacity E r) (expandFrameProgram E)
      (idealStart (expandTapes E+1) 9 (formulaWord r) (expandFrameLens E r))
      (expandFrameSteps E r) (fun z=>z.st (expandOutput E)=frame (termsWord (E.expand r))) := by
  let σ:=idealStart (expandTapes E+1) 9 (formulaWord r) (expandFrameLens E r)
  have ht : 2≤expandTapes E:=E.wf.program.twoTapes
  have hout0 : (expandOutput E).val≠0 := by change expandTapes E≠0;omega
  have hruler0 : expandRuler E≠0 := by
    intro h
    have hh:=congrArg Fin.val h
    change expandTapes E+1=0 at hh
    omega
  have houtRuler : expandOutput E≠expandRuler E := by
    intro h
    have hh:=congrArg Fin.val h
    change expandTapes E=expandTapes E+1 at hh
    omega
  obtain ⟨rf,hr,ho⟩:=E.wf.realizes r
  have hin : (fun j=>σ.st (expandMap E j))=E.wf.program.inputTapes (formulaWord r) := by
    funext j
    simp only [σ,idealStart,expandMap]
    split_ifs with hj
    · simp [RepairOrdinary.Program.inputTapes,hj]
    · have hne : (⟨j.val,by omega⟩ : Fin (expandTapes E+2))≠expandRuler E := by
        intro h
        have hh:=congrArg Fin.val h
        have:=j.isLt
        change j.val=expandTapes E+1 at hh
        omega
      simp [expandFrameLens,hne,RepairOrdinary.Program.inputTapes,hj]
  rw [←hin] at hr
  have hmap : Function.Injective (expandMap E) := by
    intro i j h
    exact Fin.ext (congrArg (fun z : Fin (expandTapes E+2)=>z.val) h)
  have hfar : ∀j,expandMap E j≠expandRuler E := by
    intro j h
    have hh:=congrArg Fin.val h
    have:=j.isLt
    change j.val=expandTapes E+1 at hh
    omega
  obtain ⟨b,he,hd⟩:=WXExec.machZ_run (cap:=expandFrameCapacity E r) hmap hfar σ hr
    (fun _=>rfl) (by simp [σ,idealStart,expandFrameLens,hruler0]) rfl le_rfl
  have bsource : b.st (expandSource E)=termsWord (E.expand r) := by
    change b.st (expandMap E E.wf.program.outputTape)=_
    rw [hd.st,ho]
  have bout : b.st (expandOutput E)=[] := by
    have hh:=hd.other (expandOutput E) (by
      intro j h
      have hv:=congrArg Fin.val h
      have:=j.isLt
      change j.val=expandTapes E at hv
      omega)
    rw [hh.1]
    change (if (expandOutput E).val=0 then frame (formulaWord r) else
      List.replicate (expandFrameLens E r (expandOutput E)) false)=[]
    rw [if_neg hout0,expandFrameLens,if_neg houtRuler]
    rfl
  have bhead : ∀i,b.sh i=0 := by
    intro i
    by_cases hx : ∃j,expandMap E j=i
    · obtain ⟨j,rfl⟩:=hx
      exact hd.sh j
    · simpa only [σ,idealStart] using (hd.other i (by intro j h;exact hx ⟨j,h⟩)).2
  have bval : ∀q,b.val q=0 := fun q=>by rw [hd.val];rfl
  have hso : expandSource E≠expandOutput E := by
    intro h
    have hh:=congrArg Fin.val h
    have:=E.wf.program.outputTape.isLt
    change E.wf.program.outputTape.val<expandTapes E at this
    change E.wf.program.outputTape.val=expandTapes E at hh
    omega
  have hc:=cpTerms_spec (expandFrameCapacity E r) (expandSource E) (expandOutput E) hso
    expandRegisters 8 expandRegisters_ne (E.expand r) [] b
    (by simpa only [List.append_nil] using bsource) (bhead _) bout (bhead _)
    (fun i=>bval _) (bval _)
    (by dsimp only [expandFrameCapacity];simp only [pow_succ];omega)
    (by dsimp only [expandFrameCapacity];simp only [pow_succ];omega)
    (by dsimp only [expandFrameCapacity];simp only [pow_succ];omega)
    (by dsimp only [expandFrameCapacity];simp only [pow_succ];omega)
    (by dsimp only [expandFrameCapacity];simp only [pow_succ];omega)
  refine ⟨_,WXExec.cast _ (WXExec.seq he hc) rfl
    (by unfold expandFrameSteps;omega),?_⟩
  change ((b.sets (expandOutput E) (frame (termsWord (E.expand r)))).seth
    (expandSource E) (termsWord (E.expand r)).length).st (expandOutput E)=_
  simp

/-- `lem:print`, paper/paper.tex: a single
ordinary machine performs actual exact expansion and physically
frames its self-delimiting signed Terms output. -/
noncomputable def framedExpandWordFunction (E : ExpandMachine) :
    WordFunction FormulaReq formulaWord (fun r=>frame (termsWord (E.expand r)))
      (fun r=>2*expandFrameSteps E r+2) :=
  wordFunction_of_ideal (expandFrameProgram E) (expandOutput E)
    (by have ht : 2≤expandTapes E:=E.wf.program.twoTapes
        change expandTapes E≠0;omega)
    (expandFrameCapacity E) (expandFrameLens E) (expandFrameSteps E) (fun _=>le_rfl) (by
      intro r
      refine ⟨?_,expandFrameProgram_run E r⟩
      unfold expandFrameLens
      rw [if_neg]
      intro h
      have hh:=congrArg Fin.val h
      change expandTapes E=expandTapes E+1 at hh
      omega)

end NearQuarticWires.StageCertNative
