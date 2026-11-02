import Proof.Quartic.StageLift.ParameterFields
import Proof.Quartic.StageMain.CallSkipLists

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain.CallSkip

/-- `sec:params` and `prop:time`, paper/paper.tex: measure an actual fixed scalar block with the binary
field reader, retaining the total number of source bits in a register. -/
def scanFixedFields : ℕ → St VV MM
  | 0 => skipS
  | n + 1 => .seq scanNat (scanFixedFields n)

/-- `sec:params` and `prop:time`, paper/paper.tex: measurement of a fixed block charges each actual
field read and counts its encoded bytes, including zero fields. -/
theorem scanFixedFields_spec (values : List ℕ) :
    ScanSpec (scanFixedFields values.length)
      (fun _ : Unit => values.flatMap natWord) atomScratch
      (fun L => values.length * (66 * (L + 1) + 1) + 1) := by
  induction values with
  | nil =>
      intro C L a hc _ rest hin hlen hW hcap
      refine (skip_spec a).mono (by simp) ?_
      rintro b rfl
      exact ⟨by simp, rfl,
        Cst.of_fr hc (Fr.set (T := [vJ]) a 0 (by simp)) (by decide),
        Fr.set a 0 (by simp [atomScratch, rdNatT]),
        by simp (config := {decide := true}) [DS.set]⟩
  | cons value values ih =>
      have hs := (scanNat_spec.map (fun _ : Unit => value)).seq ih
      simpa only [List.length_cons, List.flatMap_cons, scanFixedFields] using
        hs.weaken (by intro x hx; simp only [List.mem_append] at hx; tauto)
          (by intro L; simp only [Nat.succ_mul]; omega)

/-- `sec:params` and `lem:print`, paper/paper.tex: the actual parameter grammar has two fixed blocks
and two counted natural lists, all measured from their literal bytes. -/
def scanParameters : St VV MM :=
  .seq (scanFixedFields 37) (.seq skipNatList (.seq (scanFixedFields 9) skipNatList))

/-- `sec:params` and `lem:print`, paper/paper.tex: the shared call-length counter is increased by the
actual parameter-word length, supplying a paid witness-frame address. -/
theorem scanParameters_spec : ScanSpec scanParameters Program.parametersWord
    scalarListScratch (fun L => 4000 * (L + 1) ^ 2) := by
  have hhead : ScanSpec (scanFixedFields 37)
      (fun p : Cells.Parameters => (parameterHeadScalars p).flatMap natWord)
      atomScratch (fun L => 37 * (66 * (L + 1) + 1) + 1) := by
    intro C L a hc p rest hin hlen hW hcap
    have hs := scanFixedFields_spec (parameterHeadScalars p) C L a hc () rest hin hlen hW hcap
    simpa only [parameterHeadScalars_length] using hs
  have htail : ScanSpec (scanFixedFields 9)
      (fun p : Cells.Parameters => (parameterTailScalars p).flatMap natWord)
      atomScratch (fun L => 9 * (66 * (L + 1) + 1) + 1) := by
    intro C L a hc p rest hin hlen hW hcap
    have hs := scanFixedFields_spec (parameterTailScalars p) C L a hc () rest hin hlen hW hcap
    simpa only [parameterTailScalars_length] using hs
  have hp := skipNatList_spec.map (fun p : Cells.Parameters => p.primes.sort (· ≤ ·))
  have hf := skipNatList_spec.map (fun p : Cells.Parameters => p.factors)
  have hs := hhead.seq (hp.seq (htail.seq hf))
  have hsafe : ∀ x ∈ atomScratch, x ∈ scalarListScratch := by
    intro x hx
    exact List.mem_append_left _ hx
  intro C L a hc p rest hin hlen hW hcap
  have he := hs C L a hc p rest
    (by simpa only [parametersWord_block_layout, List.append_assoc] using hin)
    (by simpa only [parametersWord_block_layout, List.append_assoc] using hlen) hW
    (by simpa only [parametersWord_block_layout, List.append_assoc] using hcap)
  refine he.mono (by dsimp; nlinarith) ?_
  intro b hb
  refine ⟨?_, hb.unchanged, hb.constants, hb.registers.weaken ?_, ?_⟩
  · simpa only [parametersWord_block_layout, List.append_assoc] using hb.pos
  · intro x hx
    simp only [List.mem_append] at hx
    tauto
  · simpa only [parametersWord_block_layout, List.append_assoc] using hb.bytes

end NearQuarticWires.StageLift
