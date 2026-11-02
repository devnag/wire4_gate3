import Proof.Gates.Cells.Kit

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `sec:params` and `lem:print`, paper/paper.tex: decode a fixed header's natural fields into an actual
retained record store. -/
def readFixedFields (store : Fin MM) : ℕ → St VV MM
  | 0 => skipS
  | n + 1 => .seq rdNatI (.seq (.op (.wrM store t3)) (readFixedFields store n))

/-- `sec:params` and `lem:print`, paper/paper.tex: header parsing is charged by actual binary field
lengths and retains every decoded scalar in its original order. -/
theorem readFixedFields_spec (C : Ctx) (store : Fin MM) (values : List ℕ)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = values.flatMap natWord ++ rest)
    (hwidth : ∀ value ∈ values, natBitLength value + 2 ≤ C.Wd)
    (hcursor : a.rc store = (a.ram store).length) :
    Hs C (readFixedFields store values.length) a
      (30 * (values.map natBitLength).sum + 34 * values.length + 1) (fun b =>
      b.ip = a.ip + (values.flatMap natWord).length ∧
      b.ram store = a.ram store ++ values ∧ b.rc store = a.rc store + values.length ∧
      (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b rdNatT) := by
  induction values generalizing a with
  | nil =>
      refine (skip_spec a).mono (by simp) ?_
      rintro b rfl
      exact ⟨by simp, by simp, by simp, fun _ _ => ⟨rfl, rfl⟩,
        rfl, Cst.of_fr (T := [vJ]) hc (Fr.set a 0 (by simp)) (by decide),
        Fr.set a 0 (by decide)⟩
  | cons value values ih =>
      change Hs C (.seq rdNatI (.seq (.op (.wrM store t3))
        (readFixedFields store values.length))) a _ _
      have her := rdNatI_spec a hc value (values.flatMap natWord ++ rest)
        (by simpa only [List.flatMap_cons, List.append_assoc] using hin)
        (hwidth value (by simp))
      refine (Hs.seq (t2 := 30 * (values.map natBitLength).sum + 34 * values.length + 3)
        her fun b ⟨hbv, _hbfit, hbi, hbr, hbf⟩ => ?_).mono (by simp; omega) (fun _ h => h)
      have hbo : b.out = a.out := congrArg (fun t => t.1) hbr
      have hbram : b.ram = a.ram := congrArg (fun t => t.2.1) hbr
      have hbrc : b.rc = a.rc := congrArg (fun t => t.2.2.1) hbr
      have hbkin : b.kin = a.kin := congrArg (fun t => t.2.2.2.1) hbr
      have hbkout : b.kout = a.kout := congrArg (fun t => t.2.2.2.2.1) hbr
      have hbkc : b.kc = a.kc := congrArg (fun t => t.2.2.2.2.2) hbr
      have hbc : Cst b := cst_fr hc hbf
      have hbcursor : b.rc store = (b.ram store).length := by rw [hbrc, hbram]; exact hcursor
      refine (Hs.seq (t2 := 30 * (values.map natBitLength).sum + 34 * values.length + 1)
        (hs_wrM C store t3 b hbcursor.le) fun d hd => ?_).mono (by omega) (fun _ h => h)
      subst d
      have hdinput : C.inp.drop (b.put store (b.env t3)).ip = values.flatMap natWord ++ rest := by
        change C.inp.drop b.ip = _
        rw [hbi, ← List.drop_drop, hin]
        simp only [List.flatMap_cons, List.append_assoc, List.drop_left]
      have hdcur : (b.put store (b.env t3)).rc store =
          ((b.put store (b.env t3)).ram store).length := by
        simp only [DS.put, Function.update_self]
        rw [putAt, if_neg (by omega)]
        simp [hbcursor]
      have hdc : Cst (b.put store (b.env t3)) := ⟨hbc.z, hbc.one, hbc.two⟩
      refine (ih (b.put store (b.env t3)) hdc hdinput
        (fun v hv => hwidth v (by simp [hv])) hdcur).mono le_rfl ?_
      rintro e ⟨hei, heram, herc, heother, hesh, hec, hef⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, hec, hbf.trans hef⟩
      · rw [hei]
        change b.ip + _ = _
        rw [hbi, List.flatMap_cons, List.length_append]
        omega
      · rw [heram]
        simp only [DS.put, Function.update_self]
        rw [putAt, if_neg (by omega), hbv, hbram]
        simp only [List.append_assoc, List.singleton_append]
      · rw [herc]
        simp only [DS.put, Function.update_self]
        rw [hbrc]
        simp only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 values.length]
      · intro other hother
        obtain ⟨hr, hc'⟩ := heother other hother
        simpa only [DS.put, Function.update_of_ne hother, hbram, hbrc] using And.intro hr hc'
      · simpa only [DS.put, hbo, hbkin, hbkout, hbkc] using hesh

end NearQuarticWires.StageLift
