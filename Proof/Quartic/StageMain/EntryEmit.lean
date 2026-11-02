import Proof.Quartic.StageMain.EntryRequest
import Proof.Quartic.StageMain.CompactEmit
import Proof.Quartic.StageMain.Totals
import Proof.Quartic.StageMain.SampleReply

/-!
# Physical source words for one sampled predicate and mask

Step 4 of `sec:algorithm`, paper/paper.tex:
the retained finite preparation word and two binary indices form
each entry request. Only this finite word is copied for a sample;
the certificate cursor and the stored seed coefficients are preserved.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open Compact SampleCells

def emitEntryNatural (x : Fin VV) : St VV MM :=
  .seq (.op (.copy t3 x)) emitNatK

theorem emitEntryNatural_run (C : Ctx) (x : Fin VV) (hx : t3 ≠ x)
    (a : DS VV MM) (hc : Cst a) (N : ℕ) (hN : a.env x = N)
    (hW : 2 ≤ C.Wd) (hfit : natBitLength N + 2 < 2 ^ C.Wd)
    (hroom : a.kin.length + (natWord N).length ≤ C.Lk) :
    Hs C (emitEntryNatural x) a (40 * natBitLength N + 42) (fun b =>
      b.kin = a.kin ++ natWord N ∧
      (b.ip, b.out, b.ram, b.rc, b.kout, b.kc) =
        (a.ip, a.out, a.ram, a.rc, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (t3 :: emitNatT)) := by
  unfold emitEntryNatural
  refine (Hs.seq (t1 := 1) (t2 := 40 * natBitLength N + 40)
    (hs_copy C t3 x a hx) ?_).mono (by omega) (fun _ h => h)
  rintro d rfl
  have hdf : Fr a (a.set t3 (a.env x)) [t3] := Fr.set a _ (by simp)
  have hdc := Cst.of_fr hc hdf (by decide)
  have hv : (a.set t3 (a.env x)).env t3 = N := by simp [hN]
  have h := emitNatK_spec (C := C) (a.set t3 (a.env x)) hdc hW
    (by rw [hv]; exact hfit) (by rw [hv]; exact hroom)
  rw [hv] at h
  refine h.mono le_rfl ?_
  rintro e ⟨hekin, herest, hec, hefr⟩
  exact ⟨hekin, herest, hec,
    (hdf.weaken (by simp)).trans (hefr.weaken (fun _ hx => List.mem_cons_of_mem _ hx))⟩

def emitEntry : St VV MM := .seq (.op (.kem true))
  (.seq emitCompact (.seq (emitEntryNatural columnCounter) (emitEntryNatural sampleValue)))

def entryEmitScratch : List (Fin VV) := [c0, t0, t3] ++ emitNatT

theorem emitEntry_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (a : DS VV MM) (hc : Cst a)
    (hkin : a.kin = [])
    (hbits : a.ram compactStore = (Program.prepWord B1 B2 r.call r.witness).map Bool.toNat)
    (hlen : a.env compactLength = (Program.prepWord B1 B2 r.call r.witness).length)
    (hcursor : a.rc compactStore = (Program.prepWord B1 B2 r.call r.witness).length)
    (hcol : a.env columnCounter = r.column.val) (hvalue : a.env sampleValue = r.fieldValue.val)
    (hW : 2 ≤ C.Wd)
    (hfit : (Program.prepWord B1 B2 r.call r.witness).length < 2 ^ C.Wd)
    (hcolfit : natBitLength r.column.val + 2 < 2 ^ C.Wd)
    (hvaluefit : natBitLength r.fieldValue.val + 2 < 2 ^ C.Wd)
    (hroom : 1 + (entryWord r).length ≤ C.Lk) :
    Hs C emitEntry a
      (9 * (Program.prepWord B1 B2 r.call r.witness).length +
        40 * natBitLength r.column.val + 40 * natBitLength r.fieldValue.val + 94) (fun b =>
      b.kin = true :: entryWord r ∧ b.ip = a.ip ∧ b.out = a.out ∧
      b.ram = a.ram ∧ b.rc = a.rc ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      Cst b ∧ Fr a b entryEmitScratch) := by
  let bits := Program.prepWord B1 B2 r.call r.witness
  have hr : 1 + bits.length + (natWord r.column.val).length +
      (natWord r.fieldValue.val).length ≤ C.Lk := by
    simpa only [entryWord, List.length_append, bits, Nat.add_assoc] using hroom
  unfold emitEntry
  refine (Hs.seq (t1 := 1)
    (t2 := 9 * bits.length + 40 * natBitLength r.column.val +
      40 * natBitLength r.fieldValue.val + 92)
    (hs_kem C true a (by rw [hkin]; simp only [List.length_nil]; omega)) ?_).mono
      (by dsimp only [bits]; omega) (fun _ h => h)
  rintro d rfl
  let d : DS VV MM := { a with kin := a.kin ++ [true] }
  have hdc : Cst d := ⟨hc.z, hc.one, hc.two⟩
  have hdk : d.kin = [true] := by simp [d, hkin]
  refine (Hs.seq (t1 := 9 * bits.length + 6)
    (t2 := 40 * natBitLength r.column.val + 40 * natBitLength r.fieldValue.val + 85)
    ((emitCompact_run C bits d hdc hbits hlen hfit
      (by rw [hdk]; simp only [List.length_singleton]; omega)).mono
        (by change a.rc compactStore + 8 * bits.length + 6 ≤ _; rw [hcursor]; dsimp only [bits]; omega)
        (fun _ h => h)) ?_).mono (by omega) (fun _ h => h)
  rintro b ⟨hbkin, hbip, hbout, hbram, hbrc, hbkout, hbkc, hbc, hbfr⟩
  have hbrc' : b.rc = a.rc := by
    rw [hbrc]
    change Function.update a.rc compactStore bits.length = a.rc
    rw [← hcursor, Function.update_eq_self]
  have hbkin' : b.kin = [true] ++ bits := by rw [hbkin, hdk]
  refine (Hs.seq (t1 := 40 * natBitLength r.column.val + 42)
    (t2 := 40 * natBitLength r.fieldValue.val + 42)
    (emitEntryNatural_run C columnCounter (by decide) b hbc r.column.val
      ((hbfr columnCounter (by decide)).trans hcol) hW hcolfit
      (by rw [hbkin']; simp only [List.length_append, List.length_singleton]; omega)) ?_).mono
        (by omega) (fun _ h => h)
  rintro e ⟨hekin, herest, hec, hefr⟩
  have hek : e.kin = ([true] ++ bits) ++ natWord r.column.val := by rw [hekin, hbkin']
  have hev : e.env sampleValue = r.fieldValue.val :=
    (hefr sampleValue (by decide)).trans ((hbfr sampleValue (by decide)).trans hvalue)
  refine (emitEntryNatural_run C sampleValue (by decide) e hec r.fieldValue.val hev hW hvaluefit
    (by rw [hek]; simp only [List.length_append, List.length_singleton]; exact hr)).mono le_rfl ?_
  rintro f ⟨hfkin, hfrest, hfc, hffr⟩
  have hrest := hfrest.trans herest
  rcases (by simpa only [Prod.mk.injEq] using hrest) with ⟨hfi, hfo, hfr, hfrc, hfk, hfkc⟩
  refine ⟨?_, hfi.trans hbip, hfo.trans hbout, hfr.trans hbram,
    hfrc.trans hbrc', hfk.trans hbkout, hfkc.trans hbkc, hfc, ?_⟩
  · rw [hfkin, hek]
    simp only [entryWord, List.cons_append, List.nil_append, bits,
      List.append_assoc]
  · exact (hbfr.weaken (by simp [entryEmitScratch])).trans
      ((hefr.weaken (by
        intro x hx; simp only [entryEmitScratch, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)).trans
        (hffr.weaken (by
          intro x hx; simp only [entryEmitScratch, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)))

end NearQuarticWires.StageMain.Controller
