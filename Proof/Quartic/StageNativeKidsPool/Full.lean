import Proof.Quartic.StageNativeKidsPool.Body
import Proof.Quartic.StageNativeKidsPool.Frame

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Expand.PolyTab
open NearQuarticWires.Control

variable {Q R : Type} {input : R→List Bool}

/-- `lem:print`, paper/paper.tex: the
whole cold pool computation appends one real stream delimiter and
frames the measured count, width and ordered original native fields. -/
noncomputable def fullProgram (counter row : Program) : WMX (streams counter row) 16:=
  .seq (bodyProgram counter row)
    (.seq (.wm (emitC ⟨14,by unfold streams;omega⟩ (10 : Fin 16) false))
      (.wm (frameProgram counter row)))

/-- `prop:time`, paper/paper.tex: the
actual complete cold source clock includes every original-row call,
fixed-loader scan and the measured final framing pass. -/
noncomputable def fullSteps (F : Q→Family R input) (width countBudget : Q→ℕ)
    (rowBudget : R→ℕ) (records : R→List (List Bool)) (q : Q) : ℕ:=
  1000*(loadCost F width q+counterCopyCost (F q).source+countBudget q+
    initializeCost (F q).count (width q)+
    (F q).count*((F q).stepBudget rowBudget+10)+(answer (F q) records (width q)).length+1)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual cold three-field source
computes, counts and emits its complete original-order native pool,
with both true delimiters and one exact outer frame. -/
theorem full_exec {records : R→List (List Bool)} {rowBudget : R→ℕ} {countBudget : Q→ℕ}
    (F : Q→Family R input) (width : Q→ℕ)
    (counter : WordFunction Q (fun q=>(F q).source)
      (fun q=>frame (natWord (F q).count)) countBudget)
    (row : WordFunction R input (fun r=>(records r).flatMap frame) rowBudget)
    (hne : ∀r,∀xs∈records r,xs≠[]) (q : Q) :
    Runs (capacity (F q) records rowBudget (width q)) (fullProgram counter.program row.program)
      (idealStart (streams counter.program row.program) 16 (sourceWord F width q)
        (lens F width countBudget counter.program row.program q))
      (fullSteps F width countBudget rowBudget records q)
      (fun τ=>τ.st ⟨15,by unfold streams;omega⟩=frame (answer (F q) records (width q))) := by
  let cap:=capacity (F q) records rowBudget (width q)
  let OUT : Fin (streams counter.program row.program+1):=⟨14,by unfold streams;omega⟩
  let DST : Fin (streams counter.program row.program+1):=⟨15,by unfold streams;omega⟩
  let Y:=natWord (F q).count++natWord (width q)++suffix ((F q).bytes records) 0 (F q).count
  let Z:=answer (F q) records (width q)
  have hZ : Z=Y++[false]:=rfl
  obtain ⟨ideal,τ,eb,hr,hs,ho,hop,hfresh,hfreshHead⟩:=body_exec F width counter row hne q
  change ideal.st OUT=Y at ho
  change ideal.val (10 : Fin 16)=Y.length at hop
  have hend : ideal.sh OUT=(ideal.st OUT).length:=hr.out_head
  have hcap:=capacity_frame (F q) records rowBudget (width q)
  have he:=emitC_spec cap OUT (10 : Fin 16) false ideal hend (by
    rw [hop]
    change 2*Z.length+1≤cap at hcap
    rw [hZ,List.length_append] at hcap
    simp only [List.length_cons,List.length_nil] at hcap
    omega)
  let last:=appendO ideal OUT 10 [false]
  have hlast : last.st OUT=Z:=by
    change ideal.st OUT++[false]=Z
    rw [ho,←hZ]
  have hlastHead : last.sh OUT=Z.length:=by
    have hh : ideal.sh OUT=Y.length:=hend.trans (congrArg List.length ho)
    simp [last,appendO,hh,hZ]
  have hlastCounter : last.val (10 : Fin 16)=Z.length:=by
    change ideal.val (10 : Fin 16)+[false].length=Z.length
    rw [hop,hZ,List.length_append]
    simp only [Y,List.length_append]
  obtain ⟨actual,ee,hse⟩:=wxexec_sim (WXExec.wm he) τ hs
  have hsLast : SimW last actual:=hse
  have hz0 : ideal.val (0 : Fin 16)=0:=by
    have hh:=hr.call_registers 0
    change ideal.val (0 : Fin 16)=0 at hh
    exact hh
  have hz1 : ideal.val (1 : Fin 16)=0:=by
    have hh:=hr.call_registers 1
    change ideal.val (1 : Fin 16)=0 at hh
    exact hh
  have hz9 : ideal.val (9 : Fin 16)=0:=hr.count
  have houtAvoid : WMX.Avoids DST (.wm (emitC OUT (10 : Fin 16) false)):=by
    simp [WMX.Avoids,WM.Avoids,emitC,WM.fwdC,OUT,DST,Fin.ext_iff]
  have hout :=Control.WXExec.avoids ee houtAvoid
  have hf : Runs cap (.wm (frameProgram counter.program row.program)) actual (frameCost Z.length)
      (fun t=>t.st DST=frame Z):=frame_exec counter.program row.program cap Z actual
    (by
      intro k _
      have hh:=(hsLast.st OUT k).symm
      rw [hlast] at hh
      exact hh)
    (by rw [hsLast.sh];exact hlastHead)
    (hout.1.trans hfresh) (hout.2.trans hfreshHead)
    (by rw [hsLast.val];simpa [last,appendO] using hz0)
    (by rw [hsLast.val];simpa [last,appendO] using hz1)
    (by rw [hsLast.val];simpa [last,appendO] using hz9)
    (by rw [hsLast.val];exact hlastCounter) hcap
  exact (Runs.seqE eb (Runs.seqE ee hf)).cost (by
    unfold bodySteps frameCost fullSteps
    dsimp only [Z]
    omega)

/-- `lem:print`, paper/paper.tex: the
complete physical count-and-row program is an ordinary cold word
function, with every final tape-head return charged to the same clock. -/
noncomputable def poolWordFunction {records : R→List (List Bool)} {rowBudget : R→ℕ} {countBudget : Q→ℕ}
    (F : Q→Family R input) (width : Q→ℕ)
    (counter : WordFunction Q (fun q=>(F q).source)
      (fun q=>frame (natWord (F q).count)) countBudget)
    (row : WordFunction R input (fun r=>(records r).flatMap frame) rowBudget)
    (hne : ∀r,∀xs∈records r,xs≠[]) :
    WordFunction Q (sourceWord F width) (fun q=>frame (answer (F q) records (width q)))
      (fun q=>2*fullSteps F width countBudget rowBudget records q+2) :=
  wordFunction_of_ideal (fullProgram counter.program row.program)
    ⟨15,by unfold streams;omega⟩ (by change 15≠0;omega)
    (fun q=>capacity (F q) records rowBudget (width q))
    (lens F width countBudget counter.program row.program)
    (fullSteps F width countBudget rowBudget records) (fun _=>le_rfl)
    (fun q=>⟨rfl,full_exec F width counter row hne q⟩)

end NearQuarticWires.StageNativeKidsPool
