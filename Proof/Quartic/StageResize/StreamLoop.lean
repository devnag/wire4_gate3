import Proof.Quartic.StageResize.StreamField

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells
open StageLift

/-- `lem:print`, paper/paper.tex: the next actual
source marker controls the raw-field loop, without a runtime count. -/
def streamLoop : St VV MM := .loop (.eq t0 v1) streamRecordBody

def streamLoopClock (inputWidth outputWidth count : ℕ) : ℕ :=
  (12 * inputWidth + 7 * outputWidth + 22) * count + 2

/-- `lem:print` and `prop:time`, paper/paper.tex: a real end marker terminates the complete raw stream;
each field is charged once and no input read goes beyond that marker. -/
theorem streamLoop_run (C : Ctx) (inputWidth outputWidth : ℕ)
    (hpos : 0 < inputWidth) (hle : inputWidth ≤ outputWidth)
    (hcap : outputWidth < 2 ^ C.Wd) (values : List ℕ)
    (hfit : ∀ v ∈ values, v < 2 ^ inputWidth) (a : DS VV MM)
    (hc : Cst a) (hflag : a.env t0 = (streamFlag values).toNat)
    (htarget : a.env targetWidth = outputWidth)
    (hin : C.inp.drop a.ip = streamPayload inputWidth values) :
    Hs C streamLoop a (streamLoopClock inputWidth outputWidth values.length) (fun b =>
      b.env t0 = 0 ∧ b.ip = a.ip + (2 * inputWidth + 1) * values.length ∧
      b.out = a.out ++ numberRecords outputWidth values ∧
      Cst b ∧ Fr a b copyScratch) := by
  unfold streamLoop
  induction values generalizing a with
  | nil =>
      have he : (Cnd.eq t0 v1).eval a = false := by
        simp [Cnd.eval, hflag, streamFlag, hc.one]
      refine ⟨a, 2, Ex.loopF (show t0 ≠ v1 by decide) he, by simp [streamLoopClock], ?_⟩
      exact ⟨by simpa [streamFlag] using hflag, by simp, by simp [numberRecords], hc, Fr.refl _ _⟩
  | cons v vs ih =>
      have he : (Cnd.eq t0 v1).eval a = true := by
        simp [Cnd.eval, hflag, streamFlag, hc.one]
      have hinput : C.inp.drop a.ip = framePayload (binary inputWidth v) ++
          streamFlag vs :: streamPayload inputWidth vs := by
        change C.inp.drop a.ip = framePayload (binary inputWidth v) ++
          numberRecords inputWidth vs ++ [false] at hin
        rw [List.append_assoc, stream_decompose inputWidth hpos vs] at hin
        exact hin
      obtain ⟨b, n, hb, hn, hbf, hbi, hbo, hbc, hbfr⟩ :=
        streamRecordBody_run C a hc inputWidth outputWidth v (streamFlag vs)
          (streamPayload inputWidth vs) hpos (hfit v (by simp)) hle hcap
          (by simpa [streamFlag] using hflag) htarget hinput
      have hbtarget : b.env targetWidth = outputWidth := by
        rw [hbfr targetWidth (by decide), htarget]
      have hpaylen : (framePayload (binary inputWidth v)).length = 2 * inputWidth := by
        have hh := congrArg List.length (frame_decompose (binary inputWidth v))
        simp only [frame_length, binary_length, List.length_cons] at hh
        omega
      have hbin : C.inp.drop b.ip = streamPayload inputWidth vs := by
        rw [hbi]
        rw [Nat.add_assoc, ← List.drop_drop, hinput]
        simp [List.drop_append, hpaylen]
      obtain ⟨d, k, hd, hk, hdz, hdi, hdo, hdc, hdfr⟩ :=
        ih (fun w hw => hfit w (by simp [hw])) b hbc hbf hbtarget hbin
      refine ⟨d, n + k + 2, Ex.loopT (show t0 ≠ v1 by decide) he hb hd,
        ?_, hdz, ?_, ?_, hdc, hbfr.trans hdfr⟩
      · simp only [streamLoopClock, List.length_cons, Nat.mul_add, Nat.mul_one] at *
        omega
      · rw [hdi, hbi]
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        omega
      · rw [hdo, hbo]
        simp only [numberRecords, List.flatMap_cons, List.append_assoc]

end NearQuarticWires.StageResize
