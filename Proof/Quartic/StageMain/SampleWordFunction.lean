import Proof.Quartic.StageMain.Samples
import Proof.Quartic.StageGamma.RawAssembler
import Proof.Gates.CheckedPCPP.WMXReady

/-!
# Cold sampler evaluation from explicit coefficient records

`imp:seed`, paper/paper.tex, and Step 4 of `sec:algorithm`. The input contains the cached modulus, the eight seed
coefficient records, the label, and explicit zero accumulator words.
Every record is physically decoded before the Horner program executes.
The cost includes loading and rewinding; field construction is separate.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5
open FinalPass FinalPass.Hash4 FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP

structure SampleRequest where
  ell : ℕ
  modulus : ℕ
  seed : ℕ
  label : ℕ
  positive : 1 ≤ ell
  modulus_ok : GF.ModulusOk modulus ell
  label_lt : label < 2 ^ ell

def sampleStart (r : SampleRequest) : HState where
  sh := fun _ => 0
  st := ![[], [], seedWord r.ell (sampleCoefficients r.ell r.seed),
    frame (binary r.ell r.modulus), frame (binary r.ell r.label),
    frame (binary r.ell 0), frame (binary r.ell 0), frame (binary r.ell 0)]
  val := fun _ => 0
  cell := false

def sampleBank (r : SampleRequest) : Fin 26 → List Bool :=
  Fin.addCases (motive := fun _ => List Bool) (coldBank (sampleStart r)) (fun _ : Fin 1 => [])

def sampleRawWord (r : SampleRequest) : List Bool := StageGamma.rawInput (sampleBank r)

def sampleRawOutput (r : SampleRequest) : List Bool :=
  frame (binary r.ell (JoinElimination.gen r.modulus r.ell 8 r.seed r.label))

def sampleRawTime (r : SampleRequest) : ℕ := 2 * hornerCost r.ell 8 + 2

def sampleRawBudget (r : SampleRequest) : ℕ :=
  2 * StageGamma.rawCost (sampleBank r) (sampleRawTime r) + 2

theorem sampleStart_ready (r : SampleRequest) :
    HReady r.modulus r.ell r.label (sampleCoefficients r.ell r.seed) (sampleStart r) := by
  refine ⟨rfl, rfl, rfl, ⟨0, rfl⟩, rfl, ⟨0, rfl⟩, rfl, ⟨0, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

noncomputable def sampleRawMachine := Rewind.machine (WMX.wm hornerW).compile

theorem sampleRawMachine_run (r : SampleRequest) :
    ∃ A, Step sampleRawMachine (sampleRawTime r) (fun _ => 0) (sampleBank r)
      (fun _ => 0) A ∧ A ((sTape (nr := 16) (5 : Fin 8)).castAdd 1) = sampleRawOutput r := by
  obtain ⟨b, hb, _, ho, _⟩ := sampleKernel_spec (18 * r.ell + 19)
    r.modulus r.ell r.seed r.label r.modulus_ok r.positive r.label_lt le_rfl
    (sampleStart r) (sampleStart_ready r)
  obtain ⟨A, hA, hs⟩ := NearCubicGates.Close.CheckedPCPP.WXExec.readyRewound (WXExec.wm hb) (fun _ => rfl) (fun _ => rfl) rfl
  refine ⟨A, ?_, (hs 5).trans ho⟩
  obtain ⟨rc, hr, ht, hh, hs⟩ := hA
  exact ⟨rc, hr, funext hh, ht, hs⟩

/-- A fixed ordinary machine loads and evaluates the encoded sampler bank. -/
noncomputable def sampleRawWordFunction :
    WordFunction SampleRequest sampleRawWord sampleRawOutput sampleRawBudget :=
  StageGamma.rawWordFunction sampleRawMachine ((sTape (nr := 16) (5 : Fin 8)).castAdd 1)
    sampleBank sampleRawOutput sampleRawTime sampleRawMachine_run

theorem sampleStart_length (r : SampleRequest) (i : Fin 8) :
    ((sampleStart r).st i).length ≤ 16 * r.ell + 17 := by
  fin_cases i <;>
    simp [sampleStart, seedWord_length, sampleCoefficients_length, frame_length] <;> omega

theorem sampleBank_length (r : SampleRequest) (i : Fin 26) :
    (sampleBank r i).length ≤ 16 * r.ell + 17 := by
  refine Fin.addCases (m := 25) (n := 1) (fun j => ?_) (fun _ => ?_) i
  · rw [sampleBank, Fin.addCases_left]
    unfold coldBank
    split
    · exact sampleStart_length r _
    · simp
    · simp
  · simp [sampleBank]

theorem sampleRawWord_length (r : SampleRequest) :
    (sampleRawWord r).length ≤ 26 * (32 * r.ell + 35) := by
  have h := StageGamma.rawInput_length_le (sampleBank r) (16 * r.ell + 17) (sampleBank_length r)
  change (StageGamma.rawInput (sampleBank r)).length ≤ _
  omega

theorem sampleRawBudget_le (r : SampleRequest) :
    sampleRawBudget r ≤ 100000 * (r.ell + 1) ^ 2 := by
  have hl := sampleRawWord_length r
  have ht := sampleKernel_cost r.ell
  dsimp only [sampleRawBudget, StageGamma.rawCost, sampleRawTime, sampleRawWord] at *
  nlinarith

end NearQuarticWires.StageMain
