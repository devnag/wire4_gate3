import Proof.Quartic.StagePrint.OriginalPipelineBanks

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

attribute [local irreducible] firstTapes selectTapes pullTapes

/-- `lem:print`, paper/paper.tex: all tapes above the first ordinary bank are outside that bank. -/
theorem firstMap_outside {second : Bool} (i : Fin (pipelineStreams second+1))
    (h2 : i.val≠2) (hi : i.val<14 ∨ 14+firstTapes second≤ i.val) :
    ∀j,firstMap second j≠i := by
  intro j h
  have hv:=congrArg Fin.val h
  have hj:=j.isLt
  unfold firstMap at hv
  split_ifs at hv <;> simp only [Fin.val_mk] at hv <;> rcases hi with hi|hi <;> omega

/-- `lem:print`, paper/paper.tex: the blank input tapes of later ordinary banks are not auxiliary clock rulers. -/
theorem OriginalPipelineRequest.loaded_blank {second : Bool} (r : OriginalPipelineRequest second)
    (i : Fin (pipelineStreams second+1)) (hi : 13≤ i.val)
    (h0 : i.val≠13) (h1 : i.val≠14+firstTapes second)
    (h2 : i.val≠15+firstTapes second+selectTapes)
    (h3 : i.val≠16+firstTapes second+selectTapes+pullTapes) : r.loaded.st i=[] := by
  simp only [OriginalPipelineRequest.loaded,dif_neg (by omega : ¬i.val<13),
    OriginalPipelineRequest.lens,if_neg h0,if_neg h1,if_neg h2,if_neg h3,List.replicate_zero]

/-- `lem:print`, paper/paper.tex: the first ordinary call leaves every tape head at its original zero position. -/
theorem Docked.all_heads_zero {ns nr t : ℕ} {map : Fin t→Fin (ns+1)}
    {σ τ : WState ns nr} {tapes : Fin t→List Bool}
    (h : Docked map σ τ (fun _=>0) tapes) (hσ : ∀i,σ.sh i=0) : ∀i,τ.sh i=0 := by
  intro i
  by_cases hi : ∃j,map j=i
  · obtain ⟨j,rfl⟩:=hi
    exact h.sh j
  · rw [(h.other i (by intro j hj;exact hi ⟨j,hj⟩)).2,hσ]

end NearQuarticWires.StagePrint
