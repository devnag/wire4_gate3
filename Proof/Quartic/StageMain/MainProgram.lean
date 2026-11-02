import Proof.Quartic.StageMain.ActiveAcquire
import Proof.Quartic.StageMain.DefaultPass
import Proof.Quartic.Cells.ParametersDefaultWord

/-!
# One ordinary main-stage program on every branch

Step 4 of `sec:algorithm`, paper/paper.tex,
uses the actual dispatch tag to select the sampled pass or the completed
interval. Arithmetic constants, source acquisition, both branches, and
final framing are instructions of one fixed program. The bounds below
are explicit finite capacities for its arithmetic and call ports.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open SampleCells Compact StageLift

structure ActiveCapacity {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p)
    (w : List Bool) (width L B T : ℕ) extends SamplingBounds f hd w width L B T where
  source : (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length + 2 ≤ width
  seed : 8 * p.1.ellf < width
  columns : 2 ^ (c.n - p.1.k) < 2 ^ width
  total : 2 ^ (c.n - p.1.k) * p.1.Q < 2 ^ width
  output : (Program.mainWord B1 B2 c w).length + 2 ≤ width

def mainBranch : St VV MM := .ite (.eq t0 v1)
  (.seq (.op .bkI) activeAcquire) defaultMain

def mainProgram : St VV MM := .seq initP (.seq (.op (.rdI t0)) mainBranch)

noncomputable def sourceSteps (B1 B2 : ℕ) (c : Call) (w : List Bool) (T : ℕ) : ℕ :=
  match Program.dispatch B1 B2 c with
  | none => 50020
  | some p => activeAcquireCost (B1 := B1) (B2 := B2) c p w T + 20

theorem mainProgram_run_of_bounds {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    (c : Call) (w : List Bool) (width : ℕ) (input : List Bool) (L B T : ℕ)
    (hinput : input = cachedMainWord B1 B2 c w) (hwidth : 64 ≤ width)
    (hactive : ∀ (p : Program.Selected c) (hd : Program.dispatch B1 B2 c = some p),
      ActiveCapacity f hd w width L B T) :
    Hs (taggedContext width input f L B) mainProgram (a0 : DS VV MM)
      (sourceSteps B1 B2 c w T) (fun b => b.out = frame (Program.mainWord B1 B2 c w)) := by
  let C := taggedContext width input f L B
  have hsmall : 2 < 2 ^ C.Wd := lt_trans (by change 2 < width; omega) Nat.lt_two_pow_self
  unfold mainProgram
  cases hd : Program.dispatch B1 B2 c with
  | none =>
    let q := Program.admittedValue B1 B2 Builder.value c w
    have hin : C.inp = false :: (outputWord q ++ mainFieldBits B1 B2 c) := by
      change input = _
      rw [hinput]
      simp only [cachedMainWord, Program.greedyWord, Program.stageWord, hd, List.cons_append, q]
    have hmain : Program.mainWord B1 B2 c w = false :: outputWord q := by
      simp only [Program.mainWord, Program.stageWord, hd, q]
    simp only [sourceSteps, hd]
    refine (Hs.seq (t2 := 50004) (initP_spec (C := C) a0 rfl rfl rfl hsmall) ?_).mono
      (by omega) (fun _ h => h)
    rintro a ⟨hc, _hr, _hrc, hip, hout, _hkin, _hkout, _hkc, _hfr⟩
    change a.ip = 0 at hip
    change a.out = [] at hout
    refine (Hs.seq (t2 := 50001)
      (readInputBit_spec C t0 a false _ (by rw [hip, List.drop_zero, hin])) ?_).mono
        (by omega) (fun _ h => h)
    rintro b rfl
    let b : DS VV MM := { a.set t0 0 with ip := a.ip + 1 }
    have hbc : Cst b := Cst.of_fr hc (Fr.set (T := [t0]) a _ (by simp)) (by decide)
    unfold mainBranch
    refine Hs.iteF (show t0 ≠ v1 by decide)
      (by simp (config := {decide := true}) [Cnd.eval, DS.set, hc.one]) ?_
    refine (defaultMain_run C q (mainFieldBits B1 B2 c) b hbc hout
      (by simp only [b, hip, Nat.zero_add, hin, List.drop_succ_cons, List.drop_zero])
      (Cells.nondispatched_outputWord_length c w hd) (by change 26 ≤ width; omega)).mono le_rfl ?_
    intro d hdo
    rw [hmain]
    exact hdo
  | some p =>
    have hh := hactive p hd
    have hin : C.inp = true :: (callWord c ++ Program.parametersWord p.1 ++
        frame (Program.witnessPrefix c p.1 w) ++
        frame (Program.certifiedBits (Program.runCall c p w)) ++
        bitWord (Program.consistentBit (Program.runCall c p w)) ++
        frame (Program.runCall c p w).chosenSeed ++ mainFieldBits B1 B2 c) := by
      change input = _
      rw [hinput]
      simp only [cachedMainWord, Program.greedyWord, Program.stageWord, hd,
        List.cons_append, List.append_assoc]
    simp only [sourceSteps, hd]
    refine (Hs.seq (t2 := activeAcquireCost (B1 := B1) (B2 := B2) c p w T + 5)
      (initP_spec (C := C) a0 rfl rfl rfl hsmall) ?_).mono (by omega) (fun _ h => h)
    rintro a ⟨hc, hr, hrc, hip, hout, hkin, _hkout, _hkc, _hfr⟩
    change a.ip = 0 at hip
    change a.out = [] at hout
    change a.kin = [] at hkin
    refine (Hs.seq (t2 := activeAcquireCost (B1 := B1) (B2 := B2) c p w T + 3)
      (readInputBit_spec C t0 a true _ (by rw [hip, List.drop_zero, hin])) ?_).mono
        (by omega) (fun _ h => h)
    rintro b rfl
    let b : DS VV MM := { a.set t0 1 with ip := a.ip + 1 }
    have hbc : Cst b := Cst.of_fr hc (Fr.set (T := [t0]) a _ (by simp)) (by decide)
    unfold mainBranch
    refine Hs.iteT (show t0 ≠ v1 by decide)
      (by simp (config := {decide := true}) [Cnd.eval, DS.set, hc.one]) ?_
    let d : DS VV MM := { b with ip := b.ip - 1 }
    have hback : Ex C (.op .bkI) b d 1 :=
      Ex.op (OpEx.bkI b (by change 0 < a.ip + 1; omega))
    have hdc : Cst d := ⟨hbc.z, hbc.one, hbc.two⟩
    have hdip : d.ip = 0 := by dsimp only [d, b]; omega
    have hde := activeAcquire_run f hd w width input L B T hinput hh.toSamplingBounds d
      hdc hdip hout hkin (fun store => ⟨congrFun hr store, congrFun hrc store⟩) hh.source
      (lt_trans (by omega : 46 < width) Nat.lt_two_pow_self) hh.seed hh.columns hh.total hh.output
    obtain ⟨e, n, he, hn, ho⟩ := hde
    exact ⟨e, 1 + n + 1, Ex.seq hback he, by omega, ho⟩

end NearQuarticWires.StageMain.Controller
