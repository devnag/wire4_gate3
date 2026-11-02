import Proof.Quartic.StageRecovery.NaturalPrint
import Proof.Quartic.StageRecovery.MobDriver
import Proof.Gates.Expand.PrintVal

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the original support
indices are the increasing true bits below its declared atom arity. -/
def supportIndices (s V : ℕ) : List ℕ := (List.range V).filter fun i => s.testBit i

/-- `lem:print`, paper/paper.tex: one more actual
binary coordinate appends precisely its present support index. -/
theorem supportIndices_succ (s k : ℕ) :
    supportIndices s (k + 1) = supportIndices s k ++ if s.testBit k then [k] else [] := by
  unfold supportIndices
  rw [List.range_succ, List.filter_append]
  cases h : s.testBit k <;> simp [h]

/-- `lem:print`, paper/paper.tex: the physical index
order agrees with the literal canonical monomial codec. -/
theorem supportIndices_sorted (V s : ℕ) :
    ((setOf V s).sort (· ≤ ·)).map Fin.val = supportIndices s V := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact List.Pairwise.map _ (fun a b h => h) (Finset.sortedLT_sort (setOf V s)).pairwise
  · exact List.pairwise_lt_range.filter _
  · intro j
    simp only [List.mem_map, Finset.mem_sort, supportIndices, List.mem_filter,
      List.mem_range, NearCubicGates.Close.Expand.setOf, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a.isLt, ha⟩
    · rintro ⟨hj, hb⟩; exact ⟨⟨j, hj⟩, hb, rfl⟩

/-- `lem:print`, paper/paper.tex: the actual emitted
support-index count is the exact original monomial cardinality. -/
theorem supportIndices_length (V s : ℕ) : (supportIndices s V).length = (setOf V s).card := by
  rw [← supportIndices_sorted, List.length_map, Finset.length_sort]

/-- `lem:print`, paper/paper.tex: binary support scan
work, independent of the retained original support and arity. -/
def supportWork : Fin VV := ⟨119, by decide⟩
/-- `lem:print`, paper/paper.tex: the quotient of the
current support suffix after one genuine binary division. -/
def supportQuotient : Fin VV := ⟨120, by decide⟩
/-- `lem:print`, paper/paper.tex: the next original
support bit, obtained by reduction modulo two. -/
def supportBit : Fin VV := ⟨121, by decide⟩
/-- `lem:print`, paper/paper.tex: the cardinality
computed by the actual first support-bit pass. -/
def supportDegree : Fin VV := ⟨122, by decide⟩
/-- `lem:print`, paper/paper.tex: the finite support
scan counter excludes the original arity register. -/
def supportIndex : Fin VV := ⟨123, by decide⟩

/-- `lem:print`, paper/paper.tex: binary halving
recovers the current bit and retains the exact remaining support suffix. -/
def supportHalfProgram : St VV MM :=
  .seq (.op (.dm supportWork v2 supportQuotient supportBit))
    (.op (.copy supportWork supportQuotient))

/-- `lem:print`, paper/paper.tex: one actual support
step is a binary division and copy, with a fixed source clock. -/
theorem supportHalfProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (s k : ℕ) (hs : a.env supportWork = s / 2 ^ k) (hfour : 4 ≤ 2 ^ C.Wd) :
    Hs C supportHalfProgram a 3 (fun b =>
      b.env supportWork = s / 2 ^ (k + 1) ∧
      b.env supportBit = (if s.testBit k then 1 else 0) ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b [supportWork, supportQuotient, supportBit]) := by
  unfold supportHalfProgram
  refine Hs.seq (t2 := 1) (hs_dm C supportWork v2 supportQuotient supportBit a
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hc.two]; omega) (by rw [hc.two]; exact hfour)) fun b hb => ?_
  subst b
  refine (hs_copy C supportWork supportQuotient _ (by decide)).mono le_rfl ?_
  rintro b rfl
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · simp (config := {decide := true}) only [DS.set_env_self, DS.set_env_ne, hc.two, hs]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  · simpa (config := {decide := true}) only [DS.set_env_ne, DS.set_env_self, hc.two, hs, pointBit]
      using (pointBit_eq s k).symm
  · exact Cst.of_fr (T := [supportWork, supportQuotient, supportBit]) hc
      (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))) (by decide)
  · exact Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))

/-- `lem:print`, paper/paper.tex: the first binary
pass increments its support cardinality exactly at a present bit. -/
def supportCountStep : St VV MM :=
  .seq supportHalfProgram
    (.ite (.eq supportBit v1) (.op (.inc supportDegree)) skipS)

/-- `lem:print`, paper/paper.tex: the cardinality
update is checked on actual binary registers and retains all tapes. -/
theorem supportCountStep_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (s k : ℕ) (hs : a.env supportWork = s / 2 ^ k)
    (hd : a.env supportDegree = (supportIndices s k).length)
    (hfit : k + 1 < 2 ^ C.Wd) (hfour : 4 ≤ 2 ^ C.Wd) :
    Hs C supportCountStep a 6 (fun b =>
      b.env supportWork = s / 2 ^ (k + 1) ∧
      b.env supportDegree = (supportIndices s (k + 1)).length ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b [supportWork, supportQuotient, supportBit, supportDegree, vJ]) := by
  have hlen : (supportIndices s k).length ≤ k := by
    simpa only [supportIndices, List.length_range] using
      (List.length_filter_le (fun i => s.testBit i) (List.range k))
  unfold supportCountStep
  refine Hs.seq (t2 := 2) (supportHalfProgram_spec C a hc s k hs hfour)
    fun b ⟨hw, hb, hsh, hbc, hbf⟩ => ?_
  have hbd : b.env supportDegree = (supportIndices s k).length := by
    rw [hbf _ (by decide), hd]
  apply Hs.ite (c := .eq supportBit v1) (show supportBit ≠ v1 by decide)
  · intro he
    have hbit : s.testBit k = true := by
      revert he
      simp only [Cnd.eval, hb, hbc.one]
      cases s.testBit k <;> simp
    refine (hs_inc C supportDegree b (by rw [hbd]; omega)).mono le_rfl ?_
    rintro d rfl
    refine ⟨by simpa (config := {decide := true}) only [DS.set_env_ne] using hw, ?_, hsh,
      Cst.of_fr (T := [supportDegree]) hbc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans (Fr.weaken hbf (by decide)) (Fr.set _ _ (by simp))⟩
    simp [DS.set_env_self, hbd, supportIndices_succ, hbit]
  · intro he
    have hbit : s.testBit k = false := by
      revert he
      simp only [Cnd.eval, hb, hbc.one]
      cases s.testBit k <;> simp
    refine (hs_zero C vJ b).mono le_rfl ?_
    rintro d rfl
    refine ⟨by simpa (config := {decide := true}) only [DS.set_env_ne] using hw, ?_, hsh,
      Cst.of_fr (T := [vJ]) hbc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans (Fr.weaken hbf (by decide)) (Fr.set _ _ (by simp))⟩
    simp (config := {decide := true}) [DS.set, hbd, supportIndices_succ, hbit]

end NearQuarticWires.StageRecovery
