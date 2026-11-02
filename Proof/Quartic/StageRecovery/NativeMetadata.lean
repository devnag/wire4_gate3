import Proof.Quartic.StageRecovery.NativeMetadataLoad

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: the metadata
program begins from the sole literal outer input and performs both real
field loads before reading the dimensions used by the decoder header. -/
noncomputable def nativeMetadataProgram : WMX 27 10 :=
  .seq (.mach Top.loadM nativeOuterMap)
    (.seq (.mach Top.loadM nativeInnerMap) nativeDimensionsProgram)

/-- `lem:print`, paper/paper.tex: four actual
metadata registers and two actual preserved source codecs determine the
header without a width, count or output-length oracle. -/
def NativeRequest.MetadataState (r : NativeRequest) (b : WState 27 10) : Prop :=
  b.st 2 = RepairRepresentation.natWord r.modulus ∧
  b.st 4 = RepairRepresentation.natWord r.targetCount ∧ b.st 27 = [] ∧
  (∀ i, b.sh i = 0) ∧
  b.val = ![0, r.table.q, natBitLength r.modulus, r.table.count,
    natBitLength r.table.count, 0, 0, 0, 0, 0]

/-- `prop:time`, paper/paper.tex: actual input
extraction and dimension reads compose by addition of their real clocks. -/
def NativeRequest.metadataSteps (r : NativeRequest) : ℕ :=
  r.loadCost + 1 + (r.table.loadCost + 1 + r.dimensionsSteps)

/-- `lem:print`, paper/paper.tex: the complete cold
metadata program physically produces the exact native width/count and
modulus-codec length from the unchanged eleven-field outer record. -/
theorem nativeMetadataProgram_spec (cap : ℕ) (r : NativeRequest)
    (hcapQ : r.table.q + 1 ≤ cap) (hcapM : natBitLength r.modulus + 1 ≤ cap)
    (hcapN : r.table.count + 2 ≤ cap) :
    Runs cap nativeMetadataProgram (idealStart 27 10 r.word r.metadataLens)
      r.metadataSteps r.MetadataState := by
  have eO := nativeOuterLoad_spec cap r
  obtain ⟨b, eI, dock⟩ := nativeInnerLoad_spec cap r
  have hQ : b.st 16 = List.replicate r.table.q true := by
    change b.st (nativeInnerMap 3) = _
    rw [dock.st]
    rfl
  have hN : b.st 18 = List.replicate r.table.count true := by
    change b.st (nativeInnerMap 5) = _
    rw [dock.st]
    rfl
  have hOff (i : Fin 28) (hval : i.val < 14) (h3 : i ≠ 3) : ∀ j, nativeInnerMap j ≠ i := by
    intro j he
    by_cases hj0 : j.val = 0
    · have hj : nativeInnerMap j = 3 := by simp [nativeInnerMap, hj0]
      exact h3 (he.symm.trans hj)
    · have hv : j.val + 13 = i.val := by
        simpa only [nativeInnerMap, hj0, if_false, Fin.val_mk] using congrArg Fin.val he
      omega
  have hM : b.st 2 = RepairRepresentation.natWord r.modulus := by
    rw [(dock.other 2 (hOff 2 (by decide) (by decide))).1]
    rfl
  have hT : b.st 4 = RepairRepresentation.natWord r.targetCount := by
    rw [(dock.other 4 (hOff 4 (by decide) (by decide))).1]
    rfl
  have hOut : b.st 27 = [] := by
    rw [(dock.other 27 (by
      intro j h
      have hv := congrArg Fin.val h
      have := j.isLt
      simp only [nativeInnerMap] at hv
      split_ifs at hv <;> norm_num at hv <;> omega)).1]
    rfl
  have hH : ∀ i, b.sh i = 0 := by
    intro i
    by_cases h : ∃ j, nativeInnerMap j = i
    · obtain ⟨j, rfl⟩ := h
      exact dock.sh j
    · exact (dock.other i (by intro j he; exact h ⟨j, he⟩)).2
  have hV : ∀ i, b.val i = 0 := by intro i; rw [dock.val]; rfl
  have eD := nativeDimensionsProgram_spec cap r b hQ hM hN hH hV hcapQ hcapM hcapN
  refine ⟨_, eO.seq (eI.seq eD), ?_⟩
  refine ⟨hM, hT, hOut, hH, ?_⟩
  funext i
  fin_cases i <;> simp [hV]

end NearQuarticWires.StageRecovery
