import Proof.Quartic.StageMainMask.ReadyCore
import Proof.Quartic.StageMainMask.Evaluation
import Proof.Quartic.StageMain.MarkedOutput

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageMain StageLift

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
one actual native body reads the original finite Entry source, computes
all four points, runs the three cold subroutines and writes its two bits. -/
def rawEntryProgram : St VV MM := .seq entryReadyCore evaluateEntry

/-- `prop:time`, paper/paper.tex: the complete
finite source and four-point construction precede all charged ordinary
subroutine calls and the final exact predicate-mask reply. -/
noncomputable def rawEntrySteps {B1 B2 : ℕ} (r : EntryRequest B1 B2) (L B : ℕ) : ℕ :=
  entryPointCoreSteps r + evaluationSteps r L B + 122

/-- `def:mask`, Step 4 of `sec:algorithm` and `prop:time`,
paper/paper.tex:
the literal original source supplies the complete numeric Entry result
from empty stores, without points, decoded gates or table values supplied
as premises; all four-point, source and ordinary-call work is paid. -/
theorem rawEntryProgram_run {B1 B2 : ℕ} (r : EntryRequest B1 B2)
    (width : ℕ) (input : List Bool) (L B : ℕ) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a) (hin : input.drop a.ip = entryWord r ++ rest)
    (hwidth : (entryWord r).length + 2 ≤ width) (h64 : 64 ≤ width)
    (hnwidth : r.call.n + 4 ≤ width) (hkin : a.kin = [])
    (hempty : ∀ store, a.ram store = [] ∧ a.rc store = 0)
    (hcap : EntryCallCapacity r width L B) :
    Hs (entryContext B1 B2 width input L B) rawEntryProgram a (rawEntrySteps r L B)
      (fun b => b.out = a.out ++ [entryPredicate r, entryMask r]) := by
  let C := entryContext B1 B2 width input L B
  obtain ⟨b, n1, he1, hn1, hbdata, _hbip, hbout, hbc, hbstreams, hbcur, hbempty, _hbcursor⟩ :=
    entryReadyCore_run C r rest a hc hin hwidth h64 hnwidth hempty
  have hbkin : b.kin = [] := (congrArg (fun t => t.1) hbstreams).trans hkin
  obtain ⟨d, n2, he2, hn2, hd⟩ :=
    evaluateEntry_run r width input L B b hbc hbdata hbkin hbcur hbempty hcap
  exact ⟨d, n1 + n2 + 1, Ex.seq he1 he2, by unfold rawEntrySteps; omega,
    hd.trans (congrArg (fun out => out ++ [entryPredicate r, entryMask r]) hbout)⟩

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the cold native program initializes its constants and physically frames
the complete original numeric-entry answer in the required order. -/
def entryProgram : St VV MM := .seq initP (framedOutputProgram rawEntryProgram)

/-- `def:mask`, Step 4 of `sec:algorithm` and `prop:time`,
paper/paper.tex:
the cold native Entry program reads exactly the original Entry word
and produces its exact five-bit framed answer; every source, point,
subroutine, output marker and initialization step is included. -/
theorem entryProgram_run {B1 B2 : ℕ} (r : EntryRequest B1 B2)
    (width L B : ℕ) (hwidth : (entryWord r).length + 2 ≤ width) (h64 : 64 ≤ width)
    (hnwidth : r.call.n + 4 ≤ width) (hcap : EntryCallCapacity r width L B) :
    Hs (entryContext B1 B2 width (entryWord r) L B) entryProgram (a0 : DS VV MM)
      (3 * rawEntrySteps r L B + 8) (fun b => b.out = entryOutput r) := by
  let C := entryContext B1 B2 width (entryWord r) L B
  unfold entryProgram
  refine (Hs.seq (t2 := 3 * rawEntrySteps r L B + 2)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl
      (by change 2 < 2 ^ width; exact lt_trans (by omega) Nat.lt_two_pow_self)) ?_).mono
        (by omega) (fun _ h => h)
  rintro a ⟨hc, hram, hrc, hip, hout, hkin, _hkout, _hkc, _hfr⟩
  change a.ip = 0 at hip
  change a.out = [] at hout
  change a.kin = [] at hkin
  obtain ⟨b, n, he, hn, ho⟩ := rawEntryProgram_run r width (entryWord r) L B [] a hc
    (by simp only [hip, List.drop_zero, List.append_nil]) hwidth h64 hnwidth hkin
    (by intro store; exact ⟨congrFun hram store, congrFun hrc store⟩) hcap
  have hm : markOutputState a = a := by
    unfold markOutputState
    simp only [hout, List.flatMap_nil]
    rw [← hout]
  have hf := framedOutput_run he
  rw [hm] at hf
  refine ⟨{ b with out := frame b.out }, 3 * n + 2, hf, by omega, ?_⟩
  change frame b.out = entryOutput r
  rw [ho, hout, List.nil_append]
  rfl

end NearQuarticWires.StageMainMask
