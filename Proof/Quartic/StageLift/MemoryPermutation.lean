import Proof.Gates.Cells.Lang

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: a finite
permutation allocates an existing source copier a disjoint record store. -/
def permuteMemory {V M : ℕ} (e : Fin M ≃ Fin M) (a : DS V M) : DS V M :=
  { a with ram := fun i => a.ram (e.symm i), rc := fun i => a.rc (e.symm i) }

/-- `lem:print`, paper/paper.tex: a physical
record update commutes exactly with finite store relabeling. -/
theorem permute_update {M : ℕ} {α : Type} (e : Fin M ≃ Fin M)
    (f : Fin M → α) (m : Fin M) (v : α) :
    (fun i => Function.update f m v (e.symm i)) =
      Function.update (fun i => f (e.symm i)) (e m) v := by
  funext i
  by_cases hi : i = e m
  · subst i
    simp
  · have hm : e.symm i ≠ m := by
      intro h
      apply hi
      simpa using congrArg e h
    simp only [Function.update_of_ne hi, Function.update_of_ne hm]

/-- `lem:print`, paper/paper.tex: register
updates do not observe the finite names of the source stores. -/
theorem permuteMemory_set {V M : ℕ} (e : Fin M ≃ Fin M) (a : DS V M)
    (x : Fin V) (v : ℕ) :
    permuteMemory e (a.set x v) = (permuteMemory e a).set x v := rfl

/-- `lem:print`, paper/paper.tex: advancing
a real cursor is transported to the same physical relabeled store. -/
theorem permuteMemory_adv {V M : ℕ} (e : Fin M ≃ Fin M) (a : DS V M) (m : Fin M) :
    permuteMemory e (a.adv m) = (permuteMemory e a).adv (e m) := by
  simp only [permuteMemory, DS.adv, permute_update, Equiv.symm_apply_apply]

/-- `lem:print`, paper/paper.tex: a paid cursor
rewind has the same destination under the finite store permutation. -/
theorem permuteMemory_rew {V M : ℕ} (e : Fin M ≃ Fin M) (a : DS V M) (m : Fin M) :
    permuteMemory e (a.rew m) = (permuteMemory e a).rew (e m) := by
  simp only [permuteMemory, DS.rew, permute_update]

/-- `lem:print`, paper/paper.tex: actual record
writes retain the exact source values under store permutation. -/
theorem permuteMemory_put {V M : ℕ} (e : Fin M ≃ Fin M) (a : DS V M)
    (m : Fin M) (v : ℕ) :
    permuteMemory e (a.put m v) = (permuteMemory e a).put (e m) v := by
  simp only [permuteMemory, DS.put, permute_update, Equiv.symm_apply_apply]

/-- `lem:print`, paper/paper.tex: sorting one
physical source store is invariant under its finite name. -/
theorem permuteMemory_srt {V M : ℕ} (e : Fin M ≃ Fin M) (a : DS V M) (m : Fin M) :
    permuteMemory e (a.srt m) = (permuteMemory e a).srt (e m) := by
  simp only [permuteMemory, DS.srt, permute_update, Equiv.symm_apply_apply]

/-- `lem:print`, paper/paper.tex: the source
program changes only the literal record-store operands. -/
def permuteOperation {V M : ℕ} (e : Fin M ≃ Fin M) : Op V M → Op V M
  | .rdM m x => .rdM (e m) x
  | .wrM m x => .wrM (e m) x
  | .rwM m => .rwM (e m)
  | .srtM m => .srtM (e m)
  | other => other

/-- `lem:print`, paper/paper.tex: finite
branches and actual loops retain their original instruction structure. -/
def permuteProgram {V M : ℕ} (e : Fin M ≃ Fin M) : St V M → St V M
  | .op o => .op (permuteOperation e o)
  | .seq left right => .seq (permuteProgram e left) (permuteProgram e right)
  | .ite test left right => .ite test (permuteProgram e left) (permuteProgram e right)
  | .loop test body => .loop test (permuteProgram e body)

/-- `lem:print`, paper/paper.tex: every real
instruction has exactly the same clock and data after store relabeling. -/
theorem operation_permuteMemory {V M : ℕ} {C : Ctx} (e : Fin M ≃ Fin M)
    {o : Op V M} {a b : DS V M} {n : ℕ} (h : OpEx C o a b n) :
    OpEx C (permuteOperation e o) (permuteMemory e a) (permuteMemory e b) n := by
  cases h
  case rdM m x h =>
    change OpEx C (.rdM (e m) x) _ _ _
    rw [permuteMemory_adv, permuteMemory_set]
    have hr : (permuteMemory e a).ram (e m) = a.ram m := by simp [permuteMemory]
    have hc : (permuteMemory e a).rc (e m) = a.rc m := by simp [permuteMemory]
    simpa only [hr, hc] using OpEx.rdM (C := C) (e m) x (permuteMemory e a)
      (by rw [hr, hc]; exact h)
  case wrM m x h =>
    change OpEx C (.wrM (e m) x) _ _ _
    rw [permuteMemory_put]
    exact OpEx.wrM (C := C) (e m) x (permuteMemory e a) (by simpa [permuteMemory] using h)
  case rwM m =>
    change OpEx C (.rwM (e m)) _ _ _
    rw [permuteMemory_rew]
    simpa only [permuteMemory, Equiv.symm_apply_apply] using OpEx.rwM (C := C) (e m) (permuteMemory e a)
  case srtM m h =>
    change OpEx C (.srtM (e m)) _ _ _
    rw [permuteMemory_srt]
    simpa only [permuteMemory, Equiv.symm_apply_apply] using OpEx.srtM (C := C) (e m) (permuteMemory e a)
      (by simpa [permuteMemory] using h)
  all_goals
    simp only [permuteOperation, permuteMemory, DS.set, DS.called]
    constructor <;> assumption

/-- `lem:print`, paper/paper.tex: the complete
existing finite source copier is reused with unchanged actual clock,
input/output words, loop tests and callee behavior. -/
theorem execution_permuteMemory {V M : ℕ} {C : Ctx} (e : Fin M ≃ Fin M)
    {s : St V M} {a b : DS V M} {n : ℕ} (h : Ex C s a b n) :
    Ex C (permuteProgram e s) (permuteMemory e a) (permuteMemory e b) n := by
  induction h with
  | op h => exact Ex.op (operation_permuteMemory e h)
  | seq _ _ ih₁ ih₂ => exact Ex.seq ih₁ ih₂
  | iteT hc he _ ih => exact Ex.iteT hc he ih
  | iteF hc he _ ih => exact Ex.iteF hc he ih
  | loopF hc he => exact Ex.loopF hc he
  | loopT hc he _ _ ih₁ ih₂ => exact Ex.loopT hc he ih₁ ih₂
  | mono _ hnm ih => exact Ex.mono ih hnm

end NearQuarticWires.StageLift
