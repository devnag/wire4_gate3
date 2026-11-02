import Proof.Quartic.StageMain.EntryEmit
import Proof.Quartic.StageMain.EntryReply
import Proof.Quartic.StageMain.SampleTaggedCall

/-!
# One complete numeric-entry call from the main controller

Step 4 of `sec:algorithm`, paper/paper.tex,
passes the original finite source and the sampled indices through
the shared ordinary call port. The full two-bit answer is consumed
before either total is changed.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open Compact SampleCells StageGamma

variable {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}

def callEntry : St VV MM := .seq emitEntry (.seq (.op .kcall) readEntryReply)

def entryCallScratch : List (Fin VV) := entryEmitScratch ++ entryReplyScratch

theorem callEntry_run
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    (r : EntryRequest B1 B2) (width : ℕ) (input : List Bool) (L B : ℕ)
    (a : DS VV MM) (hc : Cst a) (hkin : a.kin = [])
    (hbits : a.ram compactStore = (Program.prepWord B1 B2 r.call r.witness).map Bool.toNat)
    (hlen : a.env compactLength = (Program.prepWord B1 B2 r.call r.witness).length)
    (hcursor : a.rc compactStore = (Program.prepWord B1 B2 r.call r.witness).length)
    (hcol : a.env columnCounter = r.column.val) (hvalue : a.env sampleValue = r.fieldValue.val)
    (hW : 2 ≤ width)
    (hfit : (Program.prepWord B1 B2 r.call r.witness).length < 2 ^ width)
    (hcolfit : natBitLength r.column.val + 2 < 2 ^ width)
    (hvaluefit : natBitLength r.fieldValue.val + 2 < 2 ^ width)
    (hL : 1 + (entryWord r).length ≤ L)
    (hB : (sampleTaggedCallee f).bud (.inr r) ≤ B) :
    Hs (taggedContext width input f L B) callEntry a
      (9 * (Program.prepWord B1 B2 r.call r.witness).length +
        40 * natBitLength r.column.val + 40 * natBitLength r.fieldValue.val + L + B + 110)
      (fun b => b.env predicateFlag = (entryPredicate r).toNat ∧
        b.env maskFlag = (entryMask r).toNat ∧ b.kin = [] ∧
        b.kout = entryOutput r ∧ b.kc = 5 ∧ b.ip = a.ip ∧ b.out = a.out ∧
        b.ram = a.ram ∧ b.rc = a.rc ∧ Cst b ∧ Fr a b entryCallScratch) := by
  let C := taggedContext width input f L B
  unfold callEntry
  refine (Hs.seq (t2 := (1 + L + B) + 9 + 1)
    (emitEntry_run C r a hc hkin hbits hlen hcursor hcol hvalue
      hW hfit hcolfit hvaluefit hL) ?_).mono (by omega) (fun _ h => h)
  rintro b ⟨hbkin, hbip, hbo, hbr, hbrc, hbk, hbkc, hbc, hbfr⟩
  have hin : b.kin = C.K.inw (.inr r) := hbkin
  refine Hs.seq (t1 := 1 + L + B) (t2 := 9)
    (show Hs C (.op .kcall) b (1 + L + B)
      (fun d => d = b.called (entryOutput r)) from
        Hs.op (OpEx.kcall (C := C) (.inr r) b hin hB) rfl) ?_
  rintro d rfl
  have hdc : Cst (b.called (entryOutput r)) := ⟨hbc.z, hbc.one, hbc.two⟩
  refine (readEntryReply_run C (entryPredicate r) (entryMask r)
    (b.called (entryOutput r)) hdc rfl rfl).mono le_rfl ?_
  rintro e ⟨hep, hem, hekc, hef, hec, hefr⟩
  exact ⟨hep, hem, hef.kin, hef.kout, hekc, hef.ip.trans hbip, hef.out.trans hbo,
    hef.ram.trans hbr, hef.rc.trans hbrc, hec,
    (hbfr.weaken (fun _ hx => List.mem_append_left _ hx)).trans
      (hefr.weaken (fun _ hx => List.mem_append_right _ hx))⟩

end NearQuarticWires.StageMain.Controller
