import Proof.Quartic.StageMain.SourcePrint

/-!
# The three sources of the final scalar fields

Step 4 of `sec:algorithm`, paper/paper.tex,
writes arity from the original call, selected parameter scalars from
the parameter record, and the sampled counters from registers. Each
case below is a physical read followed by the exact binary printer.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageLift

inductive FinalField where
  | arity
  | parameter (i : Fin 46)
  | register (x : Fin VV)

def FinalField.value (c : Call) (p : Cells.Parameters) (a : DS VV MM) : FinalField → ℕ
  | .arity => c.n
  | .parameter i => (parameterScalars p).getD i.val 0
  | .register x => a.env x

def FinalField.program : FinalField → St VV MM
  | .arity => printArity
  | .parameter i => printParameter i
  | .register x => printRegister x

def FinalField.Safe : FinalField → Prop
  | .arity => True
  | .parameter _ => True
  | .register x => x ∉ sourcePrintScratch

structure PrintSource (c : Call) (p : Cells.Parameters) (a : DS VV MM) : Prop where
  call : a.ram callStore = (callWord c).map Bool.toNat
  parameters : a.ram parameterStore = parameterScalars p
  callCursor : a.rc callStore ≤ (callWord c).length
  parameterCursor : a.rc parameterStore ≤ 46

theorem FinalField.value_frame (c : Call) (p : Cells.Parameters) (x : FinalField)
    (hx : x.Safe) {a b : DS VV MM} (hf : Fr a b sourcePrintScratch) :
    x.value c p b = x.value c p a := by
  cases x with
  | arity => rfl
  | parameter i => rfl
  | register r => exact hf r hx

def fieldPrintBound (c : Call) (R : ℕ) : ℕ := (callWord c).length + 70 * R + 500

theorem FinalField.run (C : Ctx) (c : Call) (p : Cells.Parameters) (x : FinalField)
    (hx : x.Safe) (R : ℕ) (a : DS VV MM) (hc : Cst a) (hs : PrintSource c p a)
    (hW : 2 ≤ C.Wd) (hindex : 46 < 2 ^ C.Wd)
    (hwidth : R + 2 ≤ C.Wd) (hfit : R + 2 < 2 ^ C.Wd)
    (hbits : natBitLength (x.value c p a) ≤ R) :
    Hs C x.program a (fieldPrintBound c R) (fun b =>
      b.out = a.out ++ natWord (x.value c p a) ∧ PrintSource c p b ∧
      (b.ip, b.ram, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b sourcePrintScratch) := by
  cases x with
  | arity =>
    have hb : natBitLength c.n ≤ R := hbits
    refine (printArity_run C c a hc hs.call hW (by omega) (by omega)).mono
      (by have hh := hs.callCursor; unfold fieldPrintBound; omega) ?_
    rintro b ⟨hbo, hbrest, hbcursor, hbother, hbc, hbfr⟩
    have hram : b.ram = a.ram := congrArg (fun t => t.2.1) hbrest
    refine ⟨hbo, ⟨hram ▸ hs.call, hram ▸ hs.parameters, ?_, ?_⟩, hbrest, hbc, hbfr⟩
    · rw [hbcursor]
      simp only [callWord, List.length_append]
      omega
    · rw [hbother _ (by decide)]
      exact hs.parameterCursor
  | parameter i =>
    have hb : natBitLength ((parameterScalars p).getD i.val 0) ≤ R := hbits
    refine (printParameter_run C p i a hc hs.parameters (by omega) hW (by omega)).mono
      (by have hh := hs.parameterCursor; have hi := i.isLt; unfold fieldPrintBound; omega) ?_
    rintro b ⟨hbo, hbrest, hbcursor, hbother, hbc, hbfr⟩
    have hram : b.ram = a.ram := congrArg (fun t => t.2.1) hbrest
    exact ⟨hbo, ⟨hram ▸ hs.call, hram ▸ hs.parameters,
      by rw [hbother _ (by decide)]; exact hs.callCursor,
      by rw [hbcursor]; exact i.isLt⟩, hbrest, hbc, hbfr⟩
  | register r =>
    have hr : r ∉ registerPrintScratch := by
      intro hmem
      apply hx
      simp only [registerPrintScratch, List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · subst r; simp [sourcePrintScratch]
      · exact List.mem_append_right _ hmem
    have ht : t3 ≠ r := by intro he; exact hr (by simp [registerPrintScratch, ← he])
    have hb : natBitLength (a.env r) ≤ R := hbits
    refine (printRegister_run C r ht a hc hW (by omega)).mono
      (by unfold fieldPrintBound; omega) ?_
    rintro b ⟨hbo, hbrest, hbc, hbfr⟩
    rcases (by simpa only [Prod.mk.injEq] using hbrest) with ⟨hbi, hbram, hbrc, hbkin, hbkout, hbkc⟩
    refine ⟨hbo, ⟨hbram ▸ hs.call, hbram ▸ hs.parameters,
      hbrc ▸ hs.callCursor, hbrc ▸ hs.parameterCursor⟩,
      by rw [hbi, hbram, hbkin, hbkout, hbkc], hbc, ?_⟩
    exact hbfr.weaken (by
      intro y hy
      simp only [registerPrintScratch, List.mem_cons] at hy
      rcases hy with hy | hy
      · subst y; simp [sourcePrintScratch]
      · exact List.mem_append_right _ hy)

end NearQuarticWires.StageMain.Controller
