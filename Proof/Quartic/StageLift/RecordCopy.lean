import Proof.Gates.Cells.Kit

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells

/-- Step 3 and `lem:print`, paper/paper.tex: a fixed finite source prefix is copied by actual record
reads and writes; no source record is supplied as an auxiliary input. -/
def copyRecords (source target : Fin MM) : ℕ → St VV MM
  | 0 => skipS
  | n + 1 => .seq (.op (.rdM source t1))
      (.seq (.op (.wrM target t1)) (copyRecords source target n))

/-- Step 3 and `lem:print`, paper/paper.tex: finite record retention pays each read, write and sequencing
step and preserves every unrelated retained source and cursor. -/
theorem copyRecords_spec (C : Ctx) (source target : Fin MM) (hne : source ≠ target)
    (values tail : List ℕ) (a : DS VV MM) (hc : Cst a)
    (hin : (a.ram source).drop (a.rc source) = values ++ tail)
    (hcursor : a.rc target = (a.ram target).length) :
    Hs C (copyRecords source target values.length) a (4 * values.length + 1) (fun b =>
      b.ram target = a.ram target ++ values ∧ b.rc target = a.rc target + values.length ∧
      b.rc source = a.rc source + values.length ∧
      (∀ store, store ≠ target → b.ram store = a.ram store) ∧
      (∀ store, store ≠ source → store ≠ target → b.rc store = a.rc store) ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [t1, vJ]) := by
  induction values generalizing a with
  | nil =>
    refine (skip_spec a).mono (by simp) ?_
    rintro b rfl
    exact ⟨by simp, by simp, by simp, fun _ _ => rfl, fun _ _ _ => rfl,
      rfl, Cst.of_fr (T := [vJ]) hc (Fr.set _ _ (by simp)) (by decide),
      (Fr.set (T := [vJ]) a 0 (by simp)).weaken (by simp)⟩
  | cons value values ih =>
    have hlen := congrArg List.length hin
    simp only [List.length_drop, List.length_append, List.length_cons] at hlen
    have hread : (a.ram source).getD (a.rc source) 0 = value := by
      have hh := congrArg List.head? hin
      simp only [List.head?_drop, List.cons_append, List.head?_cons] at hh
      rw [List.getD_eq_getElem?_getD, hh]
      rfl
    unfold copyRecords
    refine (Hs.seq (t2 := 4 * values.length + 3)
      (hs_rdM C source t1 a (by omega)) fun b hb => ?_).mono (by simp; omega) (fun _ h => h)
    subst b
    let b := (a.set t1 ((a.ram source).getD (a.rc source) 0)).adv source
    have hbc : Cst b := Cst.of_fr (T := [t1]) hc (Fr.set _ _ (by simp)) (by decide)
    have hbram : b.ram = a.ram := rfl
    have hbrc : b.rc target = a.rc target := by simp only [b, DS.adv, DS.set, Function.update_of_ne hne.symm]
    have hbcursor : b.rc target = (b.ram target).length := by rw [hbrc, hbram]; exact hcursor
    refine (Hs.seq (t2 := 4 * values.length + 1) (hs_wrM C target t1 b hbcursor.le)
      fun d hd => ?_).mono (by omega) (fun _ h => h)
    subst d
    let d := b.put target (b.env t1)
    have hbvalue : b.env t1 = value := by simpa only [b, DS.adv, DS.set_env_self] using hread
    have hdram : d.ram target = a.ram target ++ [value] := by
      simp only [d, DS.put, Function.update_self, hbrc, hbram, hbvalue, putAt]
      rw [if_neg (by omega)]
    have hdrc : d.rc target = a.rc target + 1 := by
      simp only [d, DS.put, Function.update_self, hbrc]
    have hdsrc : d.rc source = a.rc source + 1 := by
      simp only [d, b, DS.put, DS.adv, DS.set, Function.update_of_ne hne, Function.update_self]
    have hdsource : d.ram source = a.ram source := by
      simp only [d, DS.put, Function.update_of_ne hne, hbram]
    have hdinput : (d.ram source).drop (d.rc source) = values ++ tail := by
      rw [hdsource, hdsrc, ← List.drop_drop, hin]
      rfl
    have hdcursor : d.rc target = (d.ram target).length := by rw [hdrc, hdram]; simp; omega
    refine (ih d ⟨hbc.z, hbc.one, hbc.two⟩ hdinput hdcursor).mono le_rfl ?_
    rintro z ⟨hzram, hzrc, hzsrc, hzother, hzcur, hzsh, hzc, hzf⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, hzsh, hzc, ?_⟩
    · rw [hzram, hdram]
      simp only [List.singleton_append, List.append_assoc]
    · rw [hzrc, hdrc, List.length_cons]
      omega
    · rw [hzsrc, hdsrc, List.length_cons]
      omega
    · intro store hs
      rw [hzother store hs]
      simp only [d, DS.put, Function.update_of_ne hs, hbram]
    · intro store hs ht
      rw [hzcur store hs ht]
      simp only [d, b, DS.put, DS.adv, DS.set, Function.update_of_ne ht, Function.update_of_ne hs]
    · exact (Fr.set a _ (by simp)).trans hzf

end NearQuarticWires.StageLift
