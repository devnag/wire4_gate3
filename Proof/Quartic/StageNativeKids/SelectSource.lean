import Proof.Quartic.StageNativeKids.BankSelection
import Proof.Quartic.StagePrint.IndexedInput

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open StagePrint

/-- `lem:print`, paper/paper.tex: actual
first-bank serialization uses the preserved original occurrence while
all seven writer scratch registers avoid the physical bank flag. -/
def firstSourceWriter : Fin 8 ↪ Fin 16 := ⟨![7, 0, 1, 3, 4, 5, 6, 8], by decide⟩

/-- `lem:print`, paper/paper.tex: actual
second-bank serialization uses the physically computed relative index
and the same disjoint writer scratch registers. -/
def secondSourceWriter : Fin 8 ↪ Fin 16 := ⟨![11, 0, 1, 3, 4, 5, 6, 8], by decide⟩

/-- `lem:print`, paper/paper.tex: the
physical bank result chooses which real occurrence register prefixes
the unchanged retained original call source. -/
noncomputable def selectSourceProgram {ns : ℕ} (src dst : Fin (ns + 1)) : WMX ns 16 :=
  .ifr 10 (writeIndexedInput src dst secondSourceWriter 9)
    (writeIndexedInput src dst firstSourceWriter 9)

/-- `lem:print`, paper/paper.tex: the
selected source removes the actual first-bank offset exactly in the
second branch, leaving every original call byte unchanged. -/
def selectedSourceWord (firstCount occurrence : ℕ) (call : List Bool) : List Bool :=
  natWord (if firstCount ≤ occurrence then occurrence - firstCount else occurrence) ++ call

/-- `prop:time`, paper/paper.tex: physical
source selection pays actual small-index serialization, the complete
finite original-call copy, both head returns and its bank branch. -/
def selectSourceClock (occurrence sourceLength : ℕ) : ℕ :=
  writeIndexedCost occurrence sourceLength + 4

/-- `lem:print` and `prop:time`, paper/paper.tex: the computed bank bit and occurrence
registers physically construct the exact original indexed source for
the real compiler. All scalar metadata, source bytes and source heads
are preserved; no selected gate or child source is supplied as an input. -/
theorem selectSourceProgram_spec {ns : ℕ} (cap : ℕ) (src dst context role : Fin (ns + 1))
    (hsd : src ≠ dst) (firstCount occurrence : ℕ) (w : List Bool)
    (original σ : WState ns 16) (hbank : BankSelectionResult context role firstCount occurrence original σ)
    (hs : σ.st src = frame w) (hsh : σ.sh src = 0) (hd : σ.st dst = []) (hdh : σ.sh dst = 0)
    (hcap : 10 * (firstCount + occurrence + w.length + 1) + 100 ≤ cap) :
    ∃ τ, WXExec cap (selectSourceProgram src dst) σ τ (selectSourceClock occurrence w.length) ∧
      τ = σ.sets dst (frame (selectedSourceWord firstCount occurrence w)) := by
  have hwriteCap (v : ℕ) (hv : v ≤ occurrence) :
      v + 8 * natBitLength v + 4 * w.length + 20 ≤ cap := by
    have hb := NearCubicGates.Close.Dispatch.natBitLength_le_succ v
    omega
  have hcopy : σ.val (9 : Fin 16) = 0 := hbank.zeros _ (by decide)
  by_cases h : firstCount ≤ occurrence
  · have hflag : σ.val (10 : Fin 16) ≠ 0 := by
      rw [hbank.second]
      simp [h]
    have e := writeIndexedInput_exec cap src dst secondSourceWriter (9 : Fin 16) hsd
      (by decide) σ (occurrence - firstCount) w hbank.difference
      (by intro j hj; fin_cases j
          · exact False.elim (hj rfl)
          all_goals exact hbank.zeros _ (by decide))
      hcopy hs hsh hd hdh (hwriteCap _ (Nat.sub_le _ _))
    refine ⟨_, (WXExec.ifrT hflag e).mono ?_, ?_⟩
    · unfold selectSourceClock writeIndexedCost
      have hp : (occurrence - firstCount + 1) ^ 2 ≤ (occurrence + 1) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      omega
    · simp only [selectedSourceWord, if_pos h]
  · have hflag : σ.val (10 : Fin 16) = 0 := by
      rw [hbank.second]
      simp [h]
    have e := writeIndexedInput_exec cap src dst firstSourceWriter (9 : Fin 16) hsd
      (by decide) σ occurrence w hbank.original
      (by intro j hj; fin_cases j
          · exact False.elim (hj rfl)
          all_goals exact hbank.zeros _ (by decide))
      hcopy hs hsh hd hdh (hwriteCap _ le_rfl)
    refine ⟨_, (WXExec.ifrF hflag e).mono (by unfold selectSourceClock; omega), ?_⟩
    simp only [selectedSourceWord, if_neg h]

end NearQuarticWires.StageNativeKids
