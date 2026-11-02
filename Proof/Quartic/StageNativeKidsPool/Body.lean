import Proof.Quartic.StageNativeKidsPool.InitializedFields
import Proof.Quartic.StageNativeKidsPool.Capacity
import Proof.Quartic.StageNativeKidsPool.Avoids

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Expand.PolyTab
open NearQuarticWires.Control

variable {Q R : Type} {input : R→List Bool}

/-- `lem:print`, paper/paper.tex: the
complete cold raw-pool body loads its literal source, counts the actual
original children once and calls the real row printer in their order. -/
noncomputable def bodyProgram (counter row : Program) : WMX (streams counter row) 16:=
  .seq (.mach NearCubicWires.WireExponent3_5.CompilerMachine.Top.loadM (loadMap counter row))
    (.seq (counterProgram counter row) (.seq (.wm (initializeProgram counter row))
      (loopProgram (rowLayout counter row))))

/-- `prop:time`, paper/paper.tex: this
actual source-body clock includes all cold phases and each generated
row-call instruction, with its original finite row-family sum. -/
noncomputable def bodySteps (F : Q→Family R input) (width countBudget : Q→ℕ)
    (rowBudget : R→ℕ) (q : Q) : ℕ:=
  loadCost F width q+counterCopyCost (F q).source+2*countBudget q+
    initializeCost (F q).count (width q)+
    (F q).count*((F q).stepBudget rowBudget+10)+10

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual cold source produces the
complete raw ordered original pool and its measured output length.
The separate final framing tape stays literally fresh throughout. -/
theorem body_exec {records : R→List (List Bool)} {rowBudget : R→ℕ} {countBudget : Q→ℕ}
    (F : Q→Family R input) (width : Q→ℕ)
    (counter : WordFunction Q (fun q=>(F q).source)
      (fun q=>frame (natWord (F q).count)) countBudget)
    (row : WordFunction R input (fun r=>(records r).flatMap frame) rowBudget)
    (hne : ∀r,∀xs∈records r,xs≠[]) (q : Q) :
    let cap:=capacity (F q) records rowBudget (width q)
    let Y:=natWord (F q).count++natWord (width q)++suffix ((F q).bytes records) 0 (F q).count
    ∃ideal τ,
      WXExec cap (bodyProgram counter.program row.program)
        (idealStart (streams counter.program row.program) 16 (sourceWord F width q)
          (lens F width countBudget counter.program row.program q)) τ
        (bodySteps F width countBudget rowBudget q) ∧
      Ready (rowLayout counter.program row.program) (F q).source (F q).header (F q).count 0 ideal ∧
      SimW ideal τ ∧
      ideal.st ⟨14,by unfold streams;omega⟩=Y ∧ ideal.val (10 : Fin 16)=Y.length ∧
      τ.st ⟨15,by unfold streams;omega⟩=[] ∧ τ.sh ⟨15,by unfold streams;omega⟩=0 := by
  let cap:=capacity (F q) records rowBudget (width q)
  let Y:=natWord (F q).count++natWord (width q)++suffix ((F q).bytes records) 0 (F q).count
  have el:=load_spec F width countBudget counter.program row.program q cap
  obtain ⟨σc,ec,hc⟩:=counted_exec F width countBudget counter row.program q cap
    (capacity_source_copy (F q) records rowBudget (width q))
  have ei:=initialize_spec F width countBudget counter.program row.program q cap σc hc
    (capacity_initialize (F q) records rowBudget (width q))
  let σi:=initialized counter.program row.program (F q).count (width q) σc
  have hready:=initialized_ready F width countBudget counter.program row.program q σc hc
  have hp:=initialized_prefix F width countBudget counter.program row.program q σc hc
  have hf:=initialized_final F width countBudget counter.program row.program q σc hc
  have hfit : σi.val (rowLayout counter.program row.program).outputCounter+
      (suffix ((F q).bytes records) 0 (F q).count).length+1≤cap := by
    change σi.val (10 : Fin 16)+_+1≤cap
    rw [hp.2]
    simpa only [List.length_append] using capacity_suffix (F q) records rowBudget (width q)
  obtain ⟨ideal,τ,hr,er,hs,ho,hop,_⟩:=loop_suffix row (F q)
    (rowLayout counter.program row.program) cap (fun j=>hne ((F q).request j))
    (capacity_count (F q) records rowBudget (width q))
    (fun j hj=>capacity_write (F q) records rowBudget (width q) j hj)
    (fun j=>capacity_call (F q) records rowBudget (width q) j)
    (F q).count 0 σi (by omega) hready hfit
  refine ⟨ideal,τ,?_,hr,hs,?_,?_,?_,?_⟩
  · exact (WXExec.seq el (WXExec.seq ec (WXExec.seq (WXExec.wm ei) er))).mono
      (by unfold bodySteps;omega)
  · change ideal.st ⟨14,by unfold streams;omega⟩=_ at ho
    exact ho.trans (congrArg (fun xs : List Bool=>
      xs++suffix ((F q).bytes records) 0 (F q).count) hp.1)
  · change ideal.val (10 : Fin 16)=σi.val (10 : Fin 16)+_ at hop
    rw [hp.2] at hop
    simpa only [Y,List.length_append] using hop
  · have hh:=Control.WXExec.avoids er (loop_avoids_final counter.program row.program)
    exact hh.1.trans hf.1
  · have hh:=Control.WXExec.avoids er (loop_avoids_final counter.program row.program)
    exact hh.2.trans hf.2

end NearQuarticWires.StageNativeKidsPool
