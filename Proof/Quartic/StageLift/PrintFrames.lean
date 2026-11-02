import Proof.Quartic.StageLift.FrameLoop
import Proof.Quartic.Greedy.Child

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the original witness and Gamma bytes have distinct
retained stores and are copied only once for the whole print request. -/
def witnessStore : Fin MM := 3
def gammaStore : Fin MM := 4

/-- Step 3 and `lem:print`, paper/paper.tex: the complete actual print source contains the call, the
parameters, the witness frame, the Gamma frame, then its true indices. -/
theorem printInput_layout {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    Greedy.printInput r = true :: (callWord r.child.call ++
      Program.parametersWord r.child.selected.1 ++
      frame (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness) ++
      frame (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)) ++
      Greedy.printIndexWord r) := by
  unfold Greedy.printInput Program.prepWord Program.stageWord
  rw [r.child.dispatched]
  simp only [Greedy.gammaTableWord, List.cons_append, List.append_assoc]

/-- `lem:print` and Step 3, paper/paper.tex: retain the two real framed payloads before interpreting
their contents or generating any walk-indexed Formula tokens. -/
def readPrintFrames : St VV MM :=
  .seq (readFrame witnessStore) (readFrame gammaStore)

/-- `lem:print`, paper/paper.tex: both actual
frames are retained once, with linear paid input/store work and the
cursor ending exactly at the unchanged print-index suffix. -/
theorem readPrintFrames_spec (C : Ctx) (witness gamma rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = frame witness ++ frame gamma ++ rest)
    (hempty : a.ram witnessStore = [] ∧ a.rc witnessStore = 0 ∧
      a.ram gammaStore = [] ∧ a.rc gammaStore = 0) :
    Hs C readPrintFrames a (8 * witness.length + 8 * gamma.length + 9) (fun b =>
      b.ip = a.ip + (frame witness).length + (frame gamma).length ∧
      b.ram witnessStore = witness.map Bool.toNat ∧
      b.ram gammaStore = gamma.map Bool.toNat ∧
      b.rc witnessStore = witness.length ∧ b.rc gammaStore = gamma.length ∧
      (∀ store, store ≠ witnessStore → store ≠ gammaStore →
        b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [t0, t1]) := by
  unfold readPrintFrames
  refine (Hs.seq (t2 := 8 * gamma.length + 4)
    (readFrame_spec C witnessStore witness (frame gamma ++ rest) a hc
    (by simpa only [List.append_assoc] using hin)
    (by rw [hempty.1, hempty.2.1]; rfl)) fun b ⟨hbi, hbr, hbrc, hbo, hbsh, hbc, hbf⟩ => ?_).mono
      (by omega) (fun _ h => h)
  have hbin : C.inp.drop b.ip = frame gamma ++ rest := by
    rw [hbi, ← List.drop_drop, hin, List.append_assoc, List.drop_left]
  have hbg : b.ram gammaStore = [] ∧ b.rc gammaStore = 0 := by
    obtain ⟨hr, hrc⟩ := hbo gammaStore (by decide)
    rw [hr, hrc]
    exact hempty.2.2
  refine (readFrame_spec C gammaStore gamma rest b hbc hbin
    (by rw [hbg.1, hbg.2]; rfl)).mono le_rfl ?_
  rintro d ⟨hdi, hdr, hdrc, hdo, hdsh, hdc, hdf⟩
  refine ⟨by rw [hdi, hbi], ?_, ?_, ?_, ?_, ?_, hdsh.trans hbsh, hdc, hbf.trans hdf⟩
  · rw [(hdo witnessStore (by decide)).1, hbr, hempty.1]
    rfl
  · rw [hdr, hbg.1]
    rfl
  · rw [(hdo witnessStore (by decide)).2, hbrc, hempty.2.1]
    omega
  · rw [hdrc, hbg.2]
    omega
  · intro store hsw hsg
    obtain ⟨hr₁, hc₁⟩ := hdo store hsg
    obtain ⟨hr₂, hc₂⟩ := hbo store hsw
    exact ⟨hr₁.trans hr₂, hc₁.trans hc₂⟩

end NearQuarticWires.StageLift
