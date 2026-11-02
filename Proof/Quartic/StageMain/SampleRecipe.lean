import Proof.Quartic.StageMain.SampleWordFunction
import Proof.Quartic.StageMain.SampleDigits
import Proof.Quartic.StageGamma.BankRecipe

/-!
# Exact physical input records for sampler evaluation

`imp:seed`, paper/paper.tex, and the main pass: each sample uses the same eight seed coefficients and
cached modulus. This finite recipe emits the literal framed tape bank
of the cold evaluator, including coefficient order and zero work words.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain
namespace SampleCells

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open FinalPass.Hash4 FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicGates.Close.Cells NearCubicGates.Close.CheckedPCPP
open StageGamma

def seedRecipe : Writer := .seq
  (Writer.join (coefficientRegisters.reverse.map fun x =>
    .seq (.literal [true]) (Writer.binaryWord ell x).framed)) (.literal [false])

def sampleStreamRecipe : Fin 8 → Writer :=
  ![.literal [], .literal [], seedRecipe,
    (Writer.binaryWord ell modulus).framed, (Writer.binaryWord ell label).framed,
    (Writer.binaryWord ell vZ).framed, (Writer.binaryWord ell vZ).framed,
    (Writer.binaryWord ell vZ).framed]

def samplePortRecipe : Fin 26 → Writer :=
  Fin.addCases (motive := fun _ => Writer) (fun i : Fin 25 =>
    match role (ns := 7) (nr := 16) i with
    | .stream j => sampleStreamRecipe j
    | _ => .literal []) (fun _ : Fin 1 => .literal [])

def sampleRecipe : Writer := Writer.join
  (List.ofFn fun i : Fin 26 => (samplePortRecipe i).framed)

structure SampleStored (r : SampleRequest) (a : DS VV MM) : Prop where
  degree : a.env ell = r.ell
  field : a.env modulus = r.modulus
  sampleLabel : a.env label = r.label
  coeff : ∀ i, a.env (coefficient i) = Sampler.seedCoeff r.ell r.seed i

theorem seedRecipe_bits (r : SampleRequest) (a : DS VV MM) (h : SampleStored r a) :
    seedRecipe.bits a = seedWord r.ell (sampleCoefficients r.ell r.seed) := by
  simp [seedRecipe, Writer.bits, Writer.bits_join, Writer.bits_framed,
    Writer.bits_binaryWord, coefficientRegisters, sampleCoefficients, coefsRev,
    seedWord, h.degree, h.coeff]

theorem sampleStreamRecipe_bits (r : SampleRequest) (a : DS VV MM)
    (hc : Cst a) (h : SampleStored r a) (i : Fin 8) :
    (sampleStreamRecipe i).bits a = (sampleStart r).st i := by
  fin_cases i <;>
    simp [sampleStreamRecipe, sampleStart, Writer.bits, Writer.bits_framed,
      Writer.bits_binaryWord, h.degree, h.field, h.sampleLabel, hc.z, seedRecipe_bits r a h]

theorem samplePortRecipe_bits (r : SampleRequest) (a : DS VV MM)
    (hc : Cst a) (h : SampleStored r a) (i : Fin 26) :
    (samplePortRecipe i).bits a = sampleBank r i := by
  refine Fin.addCases (m := 25) (n := 1) (fun j => ?_) (fun _ => ?_) i
  · rw [samplePortRecipe, sampleBank, Fin.addCases_left, Fin.addCases_left]
    unfold coldBank
    cases hr : role (ns := 7) (nr := 16) j with
    | stream k => exact sampleStreamRecipe_bits r a hc h k
    | cell => rfl
    | reg k => rfl
  · simp [samplePortRecipe, sampleBank, Writer.bits]

theorem sampleRecipe_bits (r : SampleRequest) (a : DS VV MM)
    (hc : Cst a) (h : SampleStored r a) : sampleRecipe.bits a = sampleRawWord r := by
  simp only [sampleRecipe, Writer.bits_join, List.ofFn_eq_map, List.flatMap_map,
    Writer.bits_framed, sampleRawWord, rawInput, rawRecords, recordsWord]
  apply congrArg (List.flatMap · (List.finRange 26))
  funext i
  rw [samplePortRecipe_bits r a hc h i]

theorem seedRecipe_safe : seedRecipe.Safe := by
  simp only [seedRecipe, Writer.Safe]
  constructor
  · rw [Writer.safe_join]
    intro w hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    have hx' := List.mem_reverse.mp hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx'
    rw [Writer.Safe, Writer.safe_framed]
    constructor
    · trivial
    · dsimp [Writer.binaryWord, Writer.Safe]
      fin_cases i <;> decide
  · trivial

theorem sampleRecipe_safe : sampleRecipe.Safe := by
  rw [sampleRecipe, Writer.safe_join]
  intro w hw
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
  rw [Writer.safe_framed]
  refine Fin.addCases (m := 25) (n := 1) (fun j => ?_) (fun _ => ?_) i
  · rw [samplePortRecipe, Fin.addCases_left]
    split
    · rename_i k hk
      fin_cases k <;> first
        | exact seedRecipe_safe
        | rw [show (sampleStreamRecipe _).Safe = _ from rfl, Writer.safe_framed]
        | trivial
    · trivial
  · simp [samplePortRecipe, Writer.Safe]

/-- Every bit of the sampler bank is written by the binary source program. -/
theorem sampleRecipe_run (r : SampleRequest) (C : Ctx) (a : DS VV MM)
    (hc : Cst a) (h : SampleStored r a) (hW : 2 ≤ C.Wd)
    (hfit : ∀ x ∈ sampleRecipe.params, a.env x < 2 ^ C.Wd)
    (hroom : a.kin.length + sampleRecipe.cost a ≤ C.Lk) :
    Hs C sampleRecipe.program a (sampleRecipe.cost a) (fun b =>
      b.kin = a.kin ++ sampleRawWord r ∧
      NearCubicGates.Close.CounterMachine.CellTablesProg.SameN a b ∧
      Cst b ∧ Fr a b writerScratch) := by
  simpa only [sampleRecipe_bits r a hc h] using
    Writer.run sampleRecipe sampleRecipe_safe C a hc hW hfit hroom

end SampleCells
end NearQuarticWires.StageMain
