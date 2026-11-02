import Proof.Quartic.StagePrint.OriginalPipeline

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

attribute [local irreducible] firstTapes selectTapes pullTapes

/-- `prop:time`, paper/paper.tex: the actual clocks of original decomposition, row selection and same-center pullback are retained separately. -/
def OriginalPipelineRequest.selectBudget {second : Bool} (r : OriginalPipelineRequest second) : ℕ :=
  2*(originalRowRequest r.row.original r.row.compilerIndex).lower.budget+2
noncomputable def OriginalPipelineRequest.pullBudget {second : Bool} (r : OriginalPipelineRequest second) : ℕ :=
  StagePullback.rowCost r.row.canonicalPullback

/-- `lem:print` and `prop:time`, paper/paper.tex: four distinct blank rulers pay the literal loader and all three actual ordinary subroutine runs. -/
noncomputable def OriginalPipelineRequest.lens {second : Bool} (r : OriginalPipelineRequest second)
    (i : Fin (pipelineStreams second+1)) : ℕ :=
  if i.val=13 then r.loadCapacity else
    if i.val=14+firstTapes second then r.source.childrenBudget else
      if i.val=15+firstTapes second+selectTapes then r.selectBudget else
        if i.val=16+firstTapes second+selectTapes+pullTapes then r.pullBudget else 0


/-- `lem:print`, paper/paper.tex: all ordinary source-field tapes are empty before their actual eleven-field extraction. -/
theorem OriginalPipelineRequest.lens_small {second : Bool} (r : OriginalPipelineRequest second)
    (i : Fin (pipelineStreams second+1)) (hi : i.val<13) : r.lens i=0 := by
  have h0 : i.val≠13:=by omega
  have h1 : i.val≠14+firstTapes second:=by omega
  have h2 : i.val≠15+firstTapes second+selectTapes:=by omega
  have h3 : i.val≠16+firstTapes second+selectTapes+pullTapes:=by omega
  simp only [OriginalPipelineRequest.lens,if_neg h0,if_neg h1,if_neg h2,if_neg h3]


/-- `lem:print`, paper/paper.tex: the actual loaded state contains only the original-source/index/header fields and the untouched future blank rulers. -/
noncomputable def OriginalPipelineRequest.loaded {second : Bool} (r : OriginalPipelineRequest second) :
    WState (pipelineStreams second) 3 :=
  ⟨fun _=>0,fun i=>if h:i.val<13 then r.fields ⟨i.val,h⟩ else List.replicate (r.lens i) false,
    fun _=>0,false⟩


/-- `lem:print`, paper/paper.tex: each loaded source slot has its exact input-field contents, independently of its use by later machines. -/
theorem OriginalPipelineRequest.loaded_field {second : Bool} (r : OriginalPipelineRequest second)
    (j : Fin 14) : r.loaded.st (pipelineLoadMap second j)=
      Fin.addCases r.fields (fun _ : Fin 1=>List.replicate r.loadCapacity false) j := by
  refine Fin.addCases (motive:=fun j=>r.loaded.st (pipelineLoadMap second j)=
    Fin.addCases r.fields (fun _ : Fin 1=>List.replicate r.loadCapacity false) j)
      (fun i : Fin 13=>?_) (fun i : Fin 1=>?_) j
  · rw [Fin.addCases_left]
    simp only [OriginalPipelineRequest.loaded,pipelineLoadMap,Fin.val_castAdd,Fin.val_mk,
      dif_pos i.isLt]
  · rw [Fin.addCases_right]
    have hi : i=0:=Fin.eq_zero i
    subst hi
    simp only [OriginalPipelineRequest.loaded,pipelineLoadMap,Fin.val_natAdd,Fin.val_mk,
      Fin.val_zero,Nat.add_zero]
    simp only [show ¬(13:ℕ)<13 by omega,dif_neg,OriginalPipelineRequest.lens,
      Fin.val_mk,if_pos rfl]
    simp

/-- `lem:print`, paper/paper.tex: the initial eleven-field loader has one framed input tape and twelve empty field tapes. -/
theorem pipeline_initial_fields (w : List Bool) (i : Fin 13) :
    (![frame w,[],[],[],[],[],[],[],[],[],[],[],[]] : Fin 13→List Bool) i=
      if i.val=0 then frame w else [] := by
  fin_cases i <;> rfl

end NearQuarticWires.StagePrint
