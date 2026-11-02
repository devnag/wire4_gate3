import Proof.Quartic.StageResize.CopyLoop

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells

def padBody : St VV MM :=
  .seq (.op (.emit true)) (.seq (.op (.emit false)) (.op (.inc copied)))

def padStep (a : DS VV MM) : DS VV MM :=
  { a.set copied (a.env copied + 1) with out := a.out ++ [true, false] }

theorem padStep_fr (a : DS VV MM) : Fr a (padStep a) [copied] := by
  intro y hy
  have h : y ≠ copied := by simpa using hy
  simp [padStep, DS.set, Function.update_of_ne h]

/-- `lem:print` and `prop:time`, paper/paper.tex: one extension bit consists of two physical zero-field
emissions and one actual copied-width increment. -/
theorem padBody_run (C : Ctx) (a : DS VV MM)
    (hfit : a.env copied + 1 < 2 ^ C.Wd) :
    Hs C padBody a 5 (fun b => b = padStep a) := by
  unfold padBody
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_emit C true a) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_emit C false _) ?_
  rintro c rfl
  refine (hs_inc C copied ({a with out := (a.out ++ [true]) ++ [false]} : DS VV MM)
    hfit).mono le_rfl ?_
  rintro d rfl
  simp [padStep, DS.set, List.append_assoc]

def padLoop : St VV MM := .loop (.lt copied targetWidth) padBody

/-- `lem:print` and `prop:time`, paper/paper.tex: append exactly the missing zero bits, including no
padding when both the actual source width and target width are zero. -/
theorem padLoop_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (width : ℕ)
    (hwidth : a.env targetWidth = width) (hle : a.env copied ≤ width)
    (hcap : width < 2 ^ C.Wd) :
    Hs C padLoop a (7 * (width - a.env copied) + 2) (fun b =>
      b.env copied = width ∧
      b.out = a.out ++ Pool.fpre (List.replicate (width - a.env copied) false) ∧
      b.ip = a.ip ∧ Cst b ∧ Fr a b [copied]) := by
  let n := width - a.env copied
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env copied = a.env copied + k ∧
    b.out = a.out ++ Pool.fpre (List.replicate k false) ∧
    b.ip = a.ip ∧ Cst b ∧ Fr a b [copied]
  have hrun : Hs C (.loop (.lt copied targetWidth) padBody) a (n * (5 + 2) + 2) (I n) := by
    refine Hs.loopN (c := .lt copied targetWidth) (show copied ≠ targetWidth by decide)
      I n 5 ?_ ?_ a ?_
    · intro k hk b ⟨hbcount, hbout, hbip, hbc, hbfr⟩
      have hbt : b.env targetWidth = width := by rw [hbfr targetWidth (by decide), hwidth]
      have hlt : b.env copied < b.env targetWidth := by
        rw [hbcount, hbt]
        dsimp [n] at hk
        omega
      refine ⟨by simp [Cnd.eval, hlt], ?_⟩
      refine (padBody_run C b (by omega)).mono le_rfl ?_
      rintro c rfl
      have hmark : Pool.fpre (List.replicate (k + 1) false) =
          Pool.fpre (List.replicate k false) ++ [true, false] := by
        rw [List.replicate_succ', Pool.fpre, List.flatMap_append]
        rfl
      refine ⟨?_, ?_, hbip, hbc.of_fr (padStep_fr b) (by decide), hbfr.trans (padStep_fr b)⟩
      · simp [padStep, DS.set, hbcount, Nat.add_assoc]
      · simp [padStep, hbout, hmark, List.append_assoc]
    · intro b ⟨hbcount, _, _, _, hbfr⟩
      have hbt : b.env targetWidth = width := by rw [hbfr targetWidth (by decide), hwidth]
      have heq : b.env copied = width := by dsimp [n] at hbcount; omega
      simp [Cnd.eval, heq, hbt]
    · exact ⟨by simp, by simp [Pool.fpre], rfl, hc, Fr.refl _ _⟩
  unfold padLoop
  refine hrun.mono (by dsimp [n]; omega) ?_
  rintro b ⟨hbcount, hbout, hbip, hbc, hbfr⟩
  exact ⟨by dsimp [n] at hbcount; omega, hbout, hbip, hbc, hbfr⟩

end NearQuarticWires.StageResize
