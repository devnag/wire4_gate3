import Proof.Quartic.StageMain.CompactFrameStart

/-!
# Exact literal witness-frame retention

`sec:algorithm`, paper/paper.tex:
the preparation word retained for all samples contains the complete
framed witness, with its actual runtime length and arbitrary suffix.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Compact

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift CallSkip

def copyWitnessFrame : St VV MM := .seq copyFrameStart (.loop (.eq t0 v1) copyFrameBody)

theorem copyWitnessFrame_run (C : Ctx) (bits rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = frame bits ++ rest)
    (hcursor : a.rc compactStore = (a.ram compactStore).length)
    (hcap : a.env lengthCounter + (frame bits).length < 2 ^ C.Wd) :
    Hs C copyWitnessFrame a (11 * bits.length + 8) (fun b =>
      b.ip = a.ip + (frame bits).length ∧
      b.env lengthCounter = a.env lengthCounter + (frame bits).length ∧
      b.ram compactStore = a.ram compactStore ++ (frame bits).map Bool.toNat ∧
      b.rc compactStore = a.rc compactStore + (frame bits).length ∧
      (∀ store, store ≠ compactStore → b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b frameScratch) := by
  unfold copyWitnessFrame
  refine (Hs.seq (t2 := 11 * bits.length + 2)
    (copyFrameStart_run C a (frameFlag bits) (framePayload bits ++ rest)
      (by simpa only [frame_decompose, List.cons_append] using hin) hcursor
      (by rw [frame_length] at hcap; omega)) ?_).mono (by omega) (fun _ h => h)
  rintro b rfl
  have hf := frameStart_fr a (frameFlag bits)
  have hbc := Cst.of_fr hc hf (by decide)
  have hcursor' : (frameStart a (frameFlag bits)).rc compactStore =
      ((frameStart a (frameFlag bits)).ram compactStore).length := by
    simp [frameStart, hcursor]
  have hnext : C.inp.drop (frameStart a (frameFlag bits)).ip = framePayload bits ++ rest := by
    change C.inp.drop (a.ip + 1) = _
    rw [← List.drop_drop, hin, frame_decompose]
    rfl
  refine (copyFrameLoop_run C bits rest _ hbc
    (by simp (config := {decide := true}) [frameStart, DS.set]) hnext hcursor'
    (by simp only [frameStart, DS.set_env_self]; rw [frame_length] at hcap; omega)).mono le_rfl ?_
  rintro d ⟨_hdz, hdi, hdl, hdr, hdrc, hdo, hdrest, hdc, hdfr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hdrest, hdc, hf.trans hdfr⟩
  · rw [hdi, frame_length]
    change a.ip + 1 + 2 * bits.length = _
    omega
  · rw [hdl, frame_length]
    change a.env lengthCounter + 1 + 2 * bits.length = _
    omega
  · rw [hdr, frame_decompose]
    change (a.ram compactStore ++ [(frameFlag bits).toNat]) ++ (framePayload bits).map Bool.toNat = _
    simp only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append]
  · rw [hdrc, frame_length]
    change a.rc compactStore + 1 + 2 * bits.length = _
    omega
  · intro other ho
    simpa only [frameStart, Function.update_of_ne ho] using hdo other ho

end NearQuarticWires.StageMain.Compact
