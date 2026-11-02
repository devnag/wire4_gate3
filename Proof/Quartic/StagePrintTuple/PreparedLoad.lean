import Proof.Quartic.StagePrintTuple.KernelState
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the actual
preparation output is exactly the literal eleven-field source word
loaded by the main tuple controller. -/
theorem TermCutRequest.preparedWord_fields (r : TermCutRequest) :
    r.preparedWord=Top.loadRec (r.preparedFields 0) (r.preparedFields 1) (r.preparedFields 2)
      (r.preparedFields 3) (r.preparedFields 4) (r.preparedFields 5) (r.preparedFields 6)
      (r.preparedFields 7) (r.preparedFields 8) (r.preparedFields 9) (r.preparedFields 10) := rfl

/-- `prop:time`, paper/paper.tex: source acquisition
charges the real eleven-field loader on the actual Terms bytes. -/
def TermCutRequest.preparedLoadCost (r : TermCutRequest) : ℕ :=
  Top.loadCost (r.preparedFields 0) (r.preparedFields 1) (r.preparedFields 2)
    (r.preparedFields 3) (r.preparedFields 4) (r.preparedFields 5) (r.preparedFields 6)
    (r.preparedFields 7) (r.preparedFields 8) (r.preparedFields 9) (r.preparedFields 10)

/-- `prop:time`, paper/paper.tex: only the loader's
own finite workspace is initialized with blank storage. -/
def TermCutRequest.preparedLoadCapacity (r : TermCutRequest) : ℕ :=
  2*r.preparedWord.length+1+Top.loadChainCost
    (r.preparedFields 0) (r.preparedFields 1) (r.preparedFields 2)
    (r.preparedFields 3) (r.preparedFields 4) (r.preparedFields 5) (r.preparedFields 6)
    (r.preparedFields 7) (r.preparedFields 8) (r.preparedFields 9) (r.preparedFields 10)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual cold source extraction executes the genuine
eleven-field machine on an arbitrary disjoint controller tape bank.
Every retained source tape has its exact bytes and zero cursor, and
all controller registers remain unchanged. -/
theorem preparedLoad_run {ns nr : ℕ} (cap : ℕ) (r : TermCutRequest)
    (bank : Fin 14 → Fin (ns+1)) (hb : Function.Injective bank)
    (σ : WState ns nr)
    (hin : (fun j : Fin 14 => σ.st (bank j)) =
      Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        ![frame r.preparedWord,[],[],[],[],[],[],[],[],[],[],[],[]]
        (fun _ : Fin 1=>List.replicate r.preparedLoadCapacity false))
    (hh : ∀ j, σ.sh (bank j)=0) :
    ∃ τ, WXExec cap (.mach Top.loadM bank) σ τ r.preparedLoadCost ∧
      (∀ j : Fin 13, τ.st (bank (Fin.castAdd 1 j))=r.preparedLoadedSource j) ∧
      (∀ j : Fin 14, τ.sh (bank j)=0) ∧ τ.val=σ.val ∧ τ.cell=σ.cell ∧
      τ.st (bank 13)=List.replicate r.preparedLoadCapacity false ∧
      (∀i,(∀j,bank j≠i)→τ.st i=σ.st i ∧ τ.sh i=σ.sh i) := by
  have ld := Top.load_run (r.preparedFields 0) (r.preparedFields 1) (r.preparedFields 2)
    (r.preparedFields 3) (r.preparedFields 4) (r.preparedFields 5) (r.preparedFields 6)
    (r.preparedFields 7) (r.preparedFields 8) (r.preparedFields 9) (r.preparedFields 10)
    r.preparedLoadCapacity
    (by rw [←r.preparedWord_fields];unfold TermCutRequest.preparedLoadCapacity;omega)
    (by unfold TermCutRequest.preparedLoadCapacity;omega)
  obtain ⟨actual,hr,hhead,htape,_⟩ := ld
  change run Top.loadM r.preparedLoadCost
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
      ![frame r.preparedWord,[],[],[],[],[],[],[],[],[],[],[],[]]
      (fun _ : Fin 1=>List.replicate r.preparedLoadCapacity false))=some actual at hr
  rw [←hin] at hr
  obtain ⟨τ,he,dock⟩ := WXExec.mach_run cap hb σ hh hr
  refine ⟨τ,he,?_,?_,dock.val,dock.cell,?_,dock.other⟩
  · intro j
    rw [dock.st,htape]
    dsimp only
    rw [Fin.addCases_left,←r.preparedWord_fields]
    rfl
  · intro j
    rw [dock.sh,hhead]
  · rw [dock.st,htape]
    rfl

end NearQuarticWires.StageTuple
