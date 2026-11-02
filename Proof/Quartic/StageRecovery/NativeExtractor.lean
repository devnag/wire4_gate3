import Proof.Quartic.StageRecovery.NativeRequest

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: the cold native
input extractor is precisely the existing eleven-field loader on its
fourteen actual tapes, without an extra source parser or algorithm. -/
noncomputable def nativeExtractorProgram : WMX 13 10 := .mach Top.loadM id

/-- `prop:time`, paper/paper.tex: the extractor
uses only the fixed loader's ordinary blank ruler tape. -/
def nativeExtractorLens (r : NativeRequest) (i : Fin 14) : ℕ :=
  if i = 13 then r.loadCapacity else 0

/-- `lem:print`, paper/paper.tex: actual fixed
outer-record extraction preserves the native framed input on stream
three, with its original bytes and final source heads obtained by the
checked physical loader rather than supplied prepared streams. -/
theorem nativeExtractorProgram_loaded (r : NativeRequest) :
    Runs r.loadCapacity nativeExtractorProgram
      (idealStart 13 10 r.word (nativeExtractorLens r)) r.loadCost
      (fun b => b = r.loaded) := by
  have ld := Top.load_run (RepairRepresentation.natWord r.modulus) (frame r.table.word)
    (RepairRepresentation.natWord r.targetCount) [] [] [] [] [] [] [] [] r.loadCapacity
    (by unfold NativeRequest.loadCapacity NativeRequest.word; omega)
    (by unfold NativeRequest.loadCapacity; omega)
  obtain ⟨actual, hr, hh, ht, _⟩ := ld
  let σ := idealStart 13 10 r.word (nativeExtractorLens r)
  have hin : (fun j : Fin 14 => σ.st (id j)) =
      Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate r.loadCapacity false) := by
    funext j
    fin_cases j <;> simp [σ, idealStart, nativeExtractorLens] <;> rfl
  change run Top.loadM r.loadCost
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
      ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
      (fun _ : Fin 1 => List.replicate r.loadCapacity false)) = some actual at hr
  rw [← hin] at hr
  obtain ⟨b, hb, hdock⟩ := WXExec.mach_run r.loadCapacity (Function.injective_id :
    Function.Injective (id : Fin 14 → Fin 14)) σ (fun _ => rfl) hr
  refine ⟨b, hb, ?_⟩
  apply WState.eq
  · funext i
    change b.sh ((id : Fin 14 → Fin 14) i) = 0
    rw [hdock.sh, hh]
  · funext i
    change b.st ((id : Fin 14 → Fin 14) i) = _
    rw [hdock.st, ht]
    rfl
  · exact hdock.val
  · exact hdock.cell

/-- `lem:print`, paper/paper.tex: the cold loaded
state contains exactly the actual native framed source on stream three. -/
theorem nativeExtractorProgram_spec (r : NativeRequest) :
    Runs r.loadCapacity nativeExtractorProgram
      (idealStart 13 10 r.word (nativeExtractorLens r)) r.loadCost
      (fun b => b.st 3 = frame r.table.word) :=
  (nativeExtractorProgram_loaded r).post (by
    intro b hb
    subst b
    rfl)

/-- `prop:time`, paper/paper.tex: the actual
outer-record projection pays its entire native input and all fixed
field copies before the native table machine starts. -/
def NativeRequest.extractorBudget (r : NativeRequest) : ℕ := 2 * r.loadCost + 2

/-- `lem:print`, paper/paper.tex: a genuine cold
word function extracts exactly the already framed native table input
from the literal modulus/table/target-count outer record. -/
noncomputable def nativeExtractorWordFunction :
    WordFunction NativeRequest NativeRequest.word (fun r => frame r.table.word)
      NativeRequest.extractorBudget :=
  wordFunction_of_ideal nativeExtractorProgram 3 (by decide) NativeRequest.loadCapacity
    nativeExtractorLens NativeRequest.loadCost (fun _ => le_rfl) (by
      intro r
      exact ⟨by simp [nativeExtractorLens], nativeExtractorProgram_spec r⟩)

end NearQuarticWires.StageRecovery
