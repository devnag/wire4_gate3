import Proof.Quartic.StageTupleSetupCold.Budget
import Proof.Quartic.StageTupleSetup.OneShotCore

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms
open StageTuple

/-- `lem:print` and `prop:time`, paper/paper.tex: actual eleven-field acquisition
preserves every private helper bank outside its disjoint loader.
The complete Terms source is loaded by its literal linear byte scan. -/
theorem sourceLoad_docked {ns nr : ℕ} (cap : ℕ) (r : TermCutRequest)
    (bank : Fin 14→Fin (ns+1)) (hb : Function.Injective bank) (σ : WState ns nr)
    (hin : (fun j : Fin 14=>σ.st (bank j))=
      Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
        (fun _ : Fin 1=>List.replicate r.sourceLoadCapacity false))
    (hh : ∀j,σ.sh (bank j)=0) :
    ∃τ tout,WXExec cap (.mach Top.loadM bank) σ τ r.sourceLoadCost ∧
      Docked bank σ τ (fun _=>0) tout ∧
      ∀j : Fin 13,tout (Fin.castAdd 1 j)=r.loadedSource j := by
  obtain ⟨actual,hr,hhead,htape,_⟩:=Top.load_run
    (r.sourceFields 0) (r.sourceFields 1) (r.sourceFields 2) (r.sourceFields 3)
    (r.sourceFields 4) (r.sourceFields 5) (r.sourceFields 6) (r.sourceFields 7)
    (r.sourceFields 8) (r.sourceFields 9) (r.sourceFields 10) r.sourceLoadCapacity
    (by rw [←r.word_sourceFields];unfold TermCutRequest.sourceLoadCapacity;omega)
    (by unfold TermCutRequest.sourceLoadCapacity;omega)
  change run Top.loadM r.sourceLoadCost
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
      ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
      (fun _ : Fin 1=>List.replicate r.sourceLoadCapacity false))=some actual at hr
  rw [←hin] at hr
  obtain ⟨τ,he,hd⟩:=WXExec.mach_run cap hb σ hh hr
  refine ⟨τ,actual.final.tapes,he,⟨hd.st,?_,hd.other,hd.val,hd.cell⟩,?_⟩
  · intro j
    rw [hd.sh,hhead]
  · intro j
    rw [htape]
    dsimp only
    rw [Fin.addCases_left,←r.word_sourceFields]
    rfl

end NearQuarticWires.StageTupleSetupCold
