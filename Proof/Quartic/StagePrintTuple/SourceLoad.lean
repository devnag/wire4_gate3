import Proof.Quartic.StagePrintTuple.Request
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairRepresentation (natWord)

/-- `lem:print`, paper/paper.tex: the actual eleven
input fields retain the finite original source, common affine metadata,
walk context, original Terms, stacking width and degree separately. -/
def TermCutRequest.sourceFields (r : TermCutRequest) : Fin 11 → List Bool :=
  ![frame (callWord r.header.call),
    frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord),
    r.contextWord,termsWord r.terms,natWord r.stackWidth,natWord r.degree,
    [],[],[],[],[]]

/-- `lem:print`, paper/paper.tex: the common loader
consumes exactly the frozen actual source codec. -/
theorem TermCutRequest.word_sourceFields (r : TermCutRequest) :
    r.word = Top.loadRec (r.sourceFields 0) (r.sourceFields 1) (r.sourceFields 2)
      (r.sourceFields 3) (r.sourceFields 4) (r.sourceFields 5) (r.sourceFields 6)
      (r.sourceFields 7) (r.sourceFields 8) (r.sourceFields 9) (r.sourceFields 10) := rfl

/-- `prop:time`, paper/paper.tex: source acquisition
charges the real eleven-field loader on the actual Terms bytes. -/
def TermCutRequest.sourceLoadCost (r : TermCutRequest) : ℕ :=
  Top.loadCost (r.sourceFields 0) (r.sourceFields 1) (r.sourceFields 2)
    (r.sourceFields 3) (r.sourceFields 4) (r.sourceFields 5) (r.sourceFields 6)
    (r.sourceFields 7) (r.sourceFields 8) (r.sourceFields 9) (r.sourceFields 10)

/-- `prop:time`, paper/paper.tex: only the loader's
own finite workspace is initialized with blank storage. -/
def TermCutRequest.sourceLoadCapacity (r : TermCutRequest) : ℕ :=
  2*r.word.length+1+Top.loadChainCost
    (r.sourceFields 0) (r.sourceFields 1) (r.sourceFields 2)
    (r.sourceFields 3) (r.sourceFields 4) (r.sourceFields 5) (r.sourceFields 6)
    (r.sourceFields 7) (r.sourceFields 8) (r.sourceFields 9) (r.sourceFields 10)

/-- `lem:print`, paper/paper.tex: the real input
word and each retained source field occupy distinct loader tapes. -/
def TermCutRequest.loadedSource (r : TermCutRequest) : Fin 13 → List Bool :=
  ![frame r.word,r.word,r.sourceFields 0,r.sourceFields 1,r.sourceFields 2,
    r.sourceFields 3,r.sourceFields 4,r.sourceFields 5,r.sourceFields 6,
    r.sourceFields 7,r.sourceFields 8,r.sourceFields 9,r.sourceFields 10]

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual cold source extraction executes the genuine
eleven-field machine on an arbitrary disjoint controller tape bank.
Every retained source tape has its exact bytes and zero cursor, and
all controller registers remain unchanged. -/
theorem sourceLoad_run {ns nr : ℕ} (cap : ℕ) (r : TermCutRequest)
    (bank : Fin 14 → Fin (ns+1)) (hb : Function.Injective bank)
    (σ : WState ns nr)
    (hin : (fun j : Fin 14 => σ.st (bank j)) =
      Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
        (fun _ : Fin 1=>List.replicate r.sourceLoadCapacity false))
    (hh : ∀ j, σ.sh (bank j)=0) :
    ∃ τ, WXExec cap (.mach Top.loadM bank) σ τ r.sourceLoadCost ∧
      (∀ j : Fin 13, τ.st (bank (Fin.castAdd 1 j))=r.loadedSource j) ∧
      (∀ j : Fin 14, τ.sh (bank j)=0) ∧ τ.val=σ.val ∧ τ.cell=σ.cell := by
  have ld := Top.load_run (r.sourceFields 0) (r.sourceFields 1) (r.sourceFields 2)
    (r.sourceFields 3) (r.sourceFields 4) (r.sourceFields 5) (r.sourceFields 6)
    (r.sourceFields 7) (r.sourceFields 8) (r.sourceFields 9) (r.sourceFields 10)
    r.sourceLoadCapacity
    (by rw [←r.word_sourceFields];unfold TermCutRequest.sourceLoadCapacity;omega)
    (by unfold TermCutRequest.sourceLoadCapacity;omega)
  obtain ⟨actual,hr,hhead,htape,_⟩ := ld
  change run Top.loadM r.sourceLoadCost
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
      ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
      (fun _ : Fin 1=>List.replicate r.sourceLoadCapacity false))=some actual at hr
  rw [←hin] at hr
  obtain ⟨τ,he,dock⟩ := WXExec.mach_run cap hb σ hh hr
  refine ⟨τ,he,?_,?_,dock.val,dock.cell⟩
  · intro j
    rw [dock.st,htape]
    dsimp only
    rw [Fin.addCases_left,←r.word_sourceFields]
    rfl
  · intro j
    rw [dock.sh,hhead]

end NearQuarticWires.StageTuple
