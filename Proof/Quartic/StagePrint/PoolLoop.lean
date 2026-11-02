import Proof.Quartic.StagePrint.PoolFamily

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP

/-- `lem:print`, paper/paper.tex: the original-occurrence loop decrements its actual count before each exact indexed child computation. -/
noncomputable def poolLoopProgram (p : Program) : WMX (p.tapeCount+5) 16 :=
  .whr 14 (.seq (WMX.dec 14) (poolOccurrenceProgram p))

/-- `lem:print`, paper/paper.tex: decrementing the remaining occurrence count leaves source and accumulated caches unchanged. -/
theorem poolState_dec (p : Program) (source : List Bool) (cache : ℕ→List Bool) (j left : ℕ) :
    (poolState p source cache j (left+1)).setv 14 left=poolState p source cache j left := by
  apply WState.eq
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

/-- `prop:time`, paper/paper.tex: the counted pool loop pays every indexed call and every loop instruction. -/
def PoolFamily.loopBudget {Request : Type} {input : Request→List Bool}
    (F : PoolFamily Request input) (budget : Request→ℕ) : ℕ :=
  F.count*(F.stepBudget budget+10)+1

/-- `lem:print`, paper/paper.tex: all original occurrence caches are physically accumulated by one fixed reusable-bank loop. -/
theorem poolLoop_suffix {Request : Type} {input cache : Request→List Bool} {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>frame (cache r)) budget)
    (F : PoolFamily Request input) : ∀ left j, j+left=F.count→
    ∃ τ, WXExec (F.capacity cache budget) (poolLoopProgram f.program)
      (poolState f.program F.source (F.caches cache) j left) τ
      (left*(F.stepBudget budget+10)+1) ∧
      SimW (poolState f.program F.source (F.caches cache) F.count 0) τ := by
  intro left
  induction left with
  | zero =>
    intro j hj
    have he : j=F.count := by omega
    subst he
    refine ⟨_,?_,SimW.refl _⟩
    simpa only [poolLoopProgram,zero_mul,zero_add] using
      (WXExec.whrF (cap:=F.capacity cache budget) (r:=(14 : Fin 16))
        (P:=.seq (WMX.dec 14) (poolOccurrenceProgram f.program))
        (σ:=poolState f.program F.source (F.caches cache) F.count 0) rfl)
  | succ left ih =>
    intro j hj
    have hlt : j<F.count := by omega
    let q : Fin F.count:=⟨j,hlt⟩
    have hcap : left+1≤F.capacity cache budget := by
      unfold PoolFamily.capacity
      omega
    let σ:=poolState f.program F.source (F.caches cache) j (left+1)
    have ed:=WXExec.dec (F.capacity cache budget) (14 : Fin 16) σ hcap
    change WXExec _ _ _ (σ.setv 14 left) 1 at ed
    have ed':=ed.cast (F.capacity cache budget) (poolState_dec f.program F.source (F.caches cache) j left) le_rfl
    have hi : input (F.request q)=NearCubicWires.RepairRepresentation.natWord j++F.source := F.indexed q
    have hc : cache (F.request q)=F.caches cache j := by
      simp [PoolFamily.caches,hlt,q]
    obtain ⟨τstep,es,hs⟩:=poolState_step f (F.request q) (F.capacity cache budget)
      F.source (F.caches cache) j left hi hc (F.write_cap cache budget q)
      (F.call_cap cache budget q) (F.copy_cap cache budget q)
    obtain ⟨τend,er,hr⟩:=ih (j+1) (by omega)
    obtain ⟨τfinal,erActual,hrActual⟩:=wxexec_sim er τstep hs
    refine ⟨τfinal,?_,SimW.trans hr hrActual⟩
    have hpos : σ.val (14 : Fin 16)≠0 := by change left+1≠0;omega
    have ee:=WXExec.whrT hpos (WXExec.seq ed' es) erActual
    refine ee.mono ?_
    have hstep:=F.step_le budget q
    change poolOccurrenceCost j F.source.length (input (F.request q)).length (budget (F.request q))≤_
      at hstep
    rw [Nat.succ_mul]
    omega

/-- `lem:print`, paper/paper.tex: the empty original pool becomes the complete counted cache list, including empty-cache occurrences. -/
theorem poolLoop_exec {Request : Type} {input cache : Request→List Bool} {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>frame (cache r)) budget) (F : PoolFamily Request input) :
    ∃ τ, WXExec (F.capacity cache budget) (poolLoopProgram f.program)
      (poolState f.program F.source (F.caches cache) 0 F.count) τ (F.loopBudget budget) ∧
      SimW (poolState f.program F.source (F.caches cache) F.count 0) τ :=
  poolLoop_suffix f F F.count 0 (by omega)

end NearQuarticWires.StagePrint
