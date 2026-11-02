import Proof.Quartic.StageLift.ParameterReader

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: a retained source
store is independent of every instruction accessing another store. -/
def avoidsStoreOp {V M : ℕ} (store : Fin M) : Op V M → Prop
  | .rdM m _ | .wrM m _ | .rwM m | .srtM m => store ≠ m
  | _ => True

/-- `lem:print`, paper/paper.tex: both branches
and the repeated body must preserve each unrelated retained source. -/
def avoidsStore {V M : ℕ} (store : Fin M) : St V M → Prop
  | .op o => avoidsStoreOp store o
  | .seq s t | .ite _ s t => avoidsStore store s ∧ avoidsStore store t
  | .loop _ s => avoidsStore store s

/-- `lem:print`, paper/paper.tex: one actual
instruction leaves the data and cursor of an unrelated store intact. -/
theorem avoidsStoreOp_spec {V M : ℕ} {C : Ctx} {store : Fin M}
    {o : Op V M} {a b : DS V M} {n : ℕ} (he : OpEx C o a b n)
    (ha : avoidsStoreOp store o) :
    b.ram store = a.ram store ∧ b.rc store = a.rc store := by
  cases he <;> simp_all [avoidsStoreOp, DS.set, DS.adv, DS.put, DS.rew, DS.srt, DS.called]

/-- `lem:print`, paper/paper.tex: the physical
big-step execution preserves every store omitted by its instruction
tree, including through arbitrarily many actual loop iterations. -/
theorem avoidsStore_spec {V M : ℕ} {C : Ctx} {store : Fin M}
    {s : St V M} {a b : DS V M} {n : ℕ} (he : Ex C s a b n)
    (ha : avoidsStore store s) :
    b.ram store = a.ram store ∧ b.rc store = a.rc store := by
  induction he with
  | op he => exact avoidsStoreOp_spec he ha
  | seq _ _ ih₁ ih₂ =>
      obtain ⟨h₁, h₂⟩ := ha
      exact ⟨(ih₂ h₂).1.trans (ih₁ h₁).1, (ih₂ h₂).2.trans (ih₁ h₁).2⟩
  | iteT _ _ _ ih => exact ih ha.1
  | iteF _ _ _ ih => exact ih ha.2
  | loopF => exact ⟨rfl, rfl⟩
  | loopT _ _ _ _ ih₁ ih₂ =>
      exact ⟨(ih₂ ha).1.trans (ih₁ ha).1, (ih₂ ha).2.trans (ih₁ ha).2⟩
  | mono _ _ ih => exact ih ha

/-- `sec:params` and `lem:print`, paper/paper.tex: parameter decoding accesses only the three public
parameter stores, so it preserves a separately retained witness or table. -/
theorem readParameters_avoids (store : Fin MM)
    (hstore : store ∉ [parameterStore, primeStore, factorStore]) :
    avoidsStore store readParameters := by
  have hfixed : ∀ n m, store ≠ m → avoidsStore store (readFixedFields m n) := by
    intro n
    induction n with
    | zero => intro m hm; trivial
    | succ n ih =>
        intro m hm
        change avoidsStore store rdNatI ∧
          avoidsStore store (.seq (.op (.wrM m t3)) (readFixedFields m n))
        exact ⟨by trivial, hm, ih m hm⟩
  have hlist : ∀ m count, store ≠ m → avoidsStore store (readListFields m count) := by
    intro m count hm
    change avoidsStore store (StageRecovery.readVariable count) ∧
      avoidsStore store (readCountedFields m count)
    exact ⟨by trivial, by
      change avoidsStore store (forS fieldIndex count (readFixedFields m 1))
      exact ⟨trivial, ⟨hfixed 1 m hm, trivial⟩⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hstore
  exact ⟨hfixed 37 parameterStore hstore.1,
    hlist primeStore primeCountVar hstore.2.1,
    hfixed 9 parameterStore hstore.1,
    hlist factorStore factorCountVar hstore.2.2⟩

end NearQuarticWires.StageLift
