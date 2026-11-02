import Proof.Quartic.StageNativeKids.ReadSmall
import Proof.Quartic.StagePrintTuple.BankSplit
import Proof.Wire_3_5.FinalPassHashTable

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms
open StageTuple

/-- `lem:print`, paper/paper.tex: the
first actual original-bank size is decoded on its own five small
registers, disjoint from the original occurrence reader. -/
def bankCountReader : Fin 5 ↪ Fin 16 := ⟨![0, 1, 2, 3, 4], by decide⟩

/-- `lem:print`, paper/paper.tex: the
actual occurrence code is read on a second fixed five-register bank. -/
def occurrenceReader : Fin 5 ↪ Fin 16 := ⟨![5, 6, 7, 8, 9], by decide⟩

/-- `lem:print`, paper/paper.tex: actual
comparison uses a copy of the occurrence, preserving its original value
for the first-bank branch when subtraction would otherwise erase it. -/
def bankWorkRegisters : Fin 3 ↪ Fin 16 := ⟨![11, 2, 10], by decide⟩

/-- `lem:print`, paper/paper.tex: the
real original bank is determined by reading the actual bank size and
computed role occurrence, copying the latter, and physically comparing
the two small counters. No walk or radix value is decoded. -/
def bankSelectionProgram {ns : ℕ} (context role : Fin (ns + 1)) : WMX ns 16 :=
  .seq (.wm (readSmallProgram false context bankCountReader))
    (.seq (.wm (readSmallProgram false role occurrenceReader))
      (.seq (.wm (wcopyR 7 11 12))
        (.seq (WMX.inc 10) (.wm (bankSplitProgram bankWorkRegisters)))))

/-- `prop:time`, paper/paper.tex: the
complete actual source-bank decision has a quadratic clock in the two
small original occurrence counters, independent of the binary context. -/
def bankSelectionClock (firstCount occurrence : ℕ) : ℕ :=
  2000 * (firstCount + occurrence + 1) ^ 2

/-- `lem:print`, paper/paper.tex: the
physical bank decision preserves the original occurrence, computes the
exact second-bank relative index and actual bank bit, and clears all
other scalar registers. Only the two read source cursors advance. -/
structure BankSelectionResult {ns : ℕ} (context role : Fin (ns + 1))
    (firstCount occurrence : ℕ) (σ τ : WState ns 16) : Prop where
  original : τ.val 7 = occurrence
  difference : τ.val 11 = occurrence - firstCount
  second : τ.val 10 = (decide (firstCount ≤ occurrence)).toNat
  zeros : ∀ i, i ∉ [7, 10, 11] → τ.val i = 0
  heads : τ.sh = Function.update (Function.update σ.sh context (natWord firstCount).length)
    role (natWord occurrence).length
  tapes : τ.st = σ.st
  cell : τ.cell = σ.cell

/-- `lem:print` and `prop:time`, paper/paper.tex: actual source bytes yield the original-bank
decision with a paid finite physical computation. Empty first banks and
equality at the bank boundary use the same program and select the second
bank exactly; first-bank occurrences retain their original index. -/
theorem bankSelectionProgram_spec {ns : ℕ} (cap : ℕ) (context role : Fin (ns + 1))
    (hCR : context ≠ role) (firstCount occurrence : ℕ) (restC restR : List Bool)
    (σ : WState ns 16) (hc : σ.st context = natWord firstCount ++ restC)
    (hr : σ.st role = natWord occurrence ++ restR)
    (hch : σ.sh context = 0) (hrh : σ.sh role = 0) (hz : ∀ i, σ.val i = 0)
    (hcap : 4 * (firstCount + occurrence + 1) ≤ cap) :
    ∃ τ, WXExec cap (bankSelectionProgram context role) σ τ
      (bankSelectionClock firstCount occurrence) ∧
      BankSelectionResult context role firstCount occurrence σ τ := by
  have e1 := readSmallProgram_spec cap false context bankCountReader firstCount [] restC σ
    (by simpa only [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc,
      Bool.false_eq_true, ite_false, List.nil_append] using hc)
    hch (fun _ => hz _) (by omega)
  simp only [stp, Bool.false_eq_true, ite_false, Nat.one_mul, List.length_nil, Nat.zero_add] at e1
  let s1 := (σ.seth context (natWord firstCount).length).setv 2 firstCount
  have e2 := readSmallProgram_spec cap false role occurrenceReader occurrence [] restR s1
    (by simpa [s1, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc] using hr)
    (by simp [s1, hCR.symm, hrh])
    (by intro j; fin_cases j <;> simp [s1, occurrenceReader, hz]) (by omega)
  simp only [stp, Bool.false_eq_true, ite_false, Nat.one_mul, List.length_nil, Nat.zero_add] at e2
  let s2 := (s1.seth role (natWord occurrence).length).setv 7 occurrence
  have hv : s2.val (7 : Fin 16) = occurrence := by simp [s2]
  have e3 := wcopyR_spec cap (7 : Fin 16) 11 12 (by decide) (by decide) (by decide) s2
    (by simp [s2, s1, hz]) (by simp [s2, s1, hz]) (by rw [hv]; omega)
  rw [hv] at e3
  let s3 := s2.setv 11 occurrence
  have hflag : s3.val (10 : Fin 16) = 0 := by simp [s3, s2, s1, hz]
  have e4 := WXExec.inc cap (10 : Fin 16) s3 (by rw [hflag]; omega)
  rw [hflag, Nat.zero_add] at e4
  let s4 := s3.setv 10 1
  obtain ⟨τ, e5, hresult⟩ := bankSplitProgram_spec cap bankWorkRegisters firstCount occurrence s4
    (by simp [s4, s3, bankWorkRegisters])
    (by simp [s4, s3, s2, s1, bankWorkRegisters])
    (by simp [s4, bankWorkRegisters]) (by omega) (by omega) (by omega)
  refine ⟨τ, (WXExec.seq (.wm e1) (WXExec.seq (.wm e2)
    (WXExec.seq (.wm e3) (WXExec.seq e4 (.wm e5))))).mono ?_, ?_⟩
  · unfold bankSelectionClock
    nlinarith
  · refine ⟨?_, hresult.difference, hresult.second, ?_, ?_, ?_, ?_⟩
    · rw [hresult.other 7 (by decide)]
      simp [s4, s3, s2]
    · intro i hi
      by_cases he : i = 2
      · subst he; exact hresult.remainder
      · have hother : i ∉ [bankWorkRegisters 0, bankWorkRegisters 1, bankWorkRegisters 2] := by
          simp only [bankWorkRegisters, List.mem_cons, List.not_mem_nil, or_false,
            not_or] at hi ⊢
          tauto
        rw [hresult.other i hother]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        simp [s4, s3, s2, s1, hi.1, hi.2.1, hi.2.2, he, hz]
    · simpa [s4, s3, s2, s1] using hresult.heads
    · simpa [s4, s3, s2, s1] using hresult.tapes
    · simpa [s4, s3, s2, s1] using hresult.flag

end NearQuarticWires.StageNativeKids
