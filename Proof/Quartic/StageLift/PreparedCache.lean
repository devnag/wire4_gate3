import Proof.Quartic.StageLift.MemoryPermutation
import Proof.Quartic.StageMain.CompactEmit

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- Step 3 and `lem:print`, paper/paper.tex: the finite original preparation word has a separate
store from the normalized index bank and the retained Gamma stream. -/
def preparedStore : Fin MM := 9
def preparedLength : Fin VV := 76

/-- Step 3 and `lem:print`, paper/paper.tex: the existing compact source copier uses the free store9
without changing its instruction clock or original source semantics. -/
def preparedPermutation : Fin MM ≃ Fin MM :=
  Equiv.swap StageMain.Compact.compactStore preparedStore

private theorem permuteMemory_inverse {V M : ℕ} (e : Fin M ≃ Fin M) (a : DS V M) :
    permuteMemory e (permuteMemory e.symm a) = a := by
  cases a
  simp only [permuteMemory, Equiv.symm_symm, Equiv.apply_symm_apply]

/-- Step 3 and `lem:print`, paper/paper.tex: reuse the complete actual compact-prefix copier,
with its original finite input scans, frame handling and byte counter. -/
def acquirePreparedCacheBase : St VV MM :=
  permuteProgram preparedPermutation StageMain.Compact.acquireCompact

/-- Step 3 and `lem:print`, paper/paper.tex: the real finite prepWord is retained once, before
the Gamma suffix. Neither decoded geometry nor a supplied prefix length
is an input to this physical acquisition program. -/
theorem acquirePreparedCacheBase_spec (C : Ctx) (c : Call) (p : Cells.Parameters)
    (witness rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = StageMain.Compact.compactInput c p witness ++ rest)
    (hW : (preparedPrefixWord c p).length + 2 ≤ C.Wd)
    (hcap : (StageMain.Compact.compactInput c p witness).length < 2 ^ C.Wd)
    (hempty : a.ram preparedStore = [] ∧ a.rc preparedStore = 0) :
    Hs C acquirePreparedCacheBase a (StageMain.Compact.acquireCost c p witness) (fun b =>
      b.ip = a.ip + (StageMain.Compact.compactInput c p witness).length ∧
      b.env StageMain.Compact.compactLength = (StageMain.Compact.compactInput c p witness).length ∧
      b.ram preparedStore = (StageMain.Compact.compactInput c p witness).map Bool.toNat ∧
      b.rc preparedStore = (StageMain.Compact.compactInput c p witness).length ∧
      (∀ store, store ≠ preparedStore → b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b StageMain.Compact.acquireScratch) := by
  let old := permuteMemory preparedPermutation.symm a
  have hold : Cst old := ⟨hc.z, hc.one, hc.two⟩
  have he0 : old.ram StageMain.Compact.compactStore = [] ∧
      old.rc StageMain.Compact.compactStore = 0 := by
    simpa only [old, permuteMemory, preparedPermutation, Equiv.symm_symm,
      Equiv.swap_apply_left] using hempty
  obtain ⟨b, n, he, hn, hbip, hblen, _hb108, hbram, hbrc, hbo, hbsh, hbc, hbfr⟩ :=
    StageMain.Compact.acquireCompact_run C c p witness rest old hold hin hW hcap he0
  have hex : Ex C acquirePreparedCacheBase a (permuteMemory preparedPermutation b) n := by
    simpa only [acquirePreparedCacheBase, old, permuteMemory_inverse] using
      execution_permuteMemory preparedPermutation he
  refine ⟨permuteMemory preparedPermutation b, n, hex, hn, hbip, hblen, ?_, ?_, ?_, hbsh,
    ⟨hbc.z, hbc.one, hbc.two⟩, ?_⟩
  · change b.ram (preparedPermutation.symm preparedStore) = _
    simpa only [preparedPermutation, Equiv.symm_swap, Equiv.swap_apply_right] using hbram
  · change b.rc (preparedPermutation.symm preparedStore) = _
    simpa only [preparedPermutation, Equiv.symm_swap, Equiv.swap_apply_right] using hbrc
  · intro store hs
    have hne : preparedPermutation.symm store ≠ StageMain.Compact.compactStore := by
      intro h
      apply hs
      have hh := congrArg preparedPermutation h
      simpa only [Equiv.apply_symm_apply, preparedPermutation, Equiv.swap_apply_left] using hh
    obtain ⟨hr, hc'⟩ := hbo _ hne
    refine ⟨?_, ?_⟩
    · change b.ram (preparedPermutation.symm store) = _
      rw [hr]
      simp only [old, permuteMemory, Equiv.symm_symm, Equiv.apply_symm_apply]
    · change b.rc (preparedPermutation.symm store) = _
      rw [hc']
      simp only [old, permuteMemory, Equiv.symm_symm, Equiv.apply_symm_apply]
  · intro x hx
    exact hbfr x hx

/-- Step 3 and `lem:print`, paper/paper.tex: retain the physically counted prefix length outside
binomial and coefficient workspace for all subsequent source queries. -/
def acquirePreparedCache : St VV MM :=
  .seq acquirePreparedCacheBase (.op (.copy preparedLength StageMain.Compact.compactLength))

/-- Step 3 and `lem:print`, paper/paper.tex: source caching produces its real reusable prefix and
length while preserving every other retained source and cursor. -/
theorem acquirePreparedCache_spec (C : Ctx) (c : Call) (p : Cells.Parameters)
    (witness rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = StageMain.Compact.compactInput c p witness ++ rest)
    (hW : (preparedPrefixWord c p).length + 2 ≤ C.Wd)
    (hcap : (StageMain.Compact.compactInput c p witness).length < 2 ^ C.Wd)
    (hempty : a.ram preparedStore = [] ∧ a.rc preparedStore = 0) :
    Hs C acquirePreparedCache a (StageMain.Compact.acquireCost c p witness + 2) (fun b =>
      b.ip = a.ip + (StageMain.Compact.compactInput c p witness).length ∧
      b.env preparedLength = (StageMain.Compact.compactInput c p witness).length ∧
      b.ram preparedStore = (StageMain.Compact.compactInput c p witness).map Bool.toNat ∧
      b.rc preparedStore = (StageMain.Compact.compactInput c p witness).length ∧
      (∀ store, store ≠ preparedStore → b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (preparedLength :: StageMain.Compact.acquireScratch)) := by
  unfold acquirePreparedCache
  refine Hs.seq (t2 := 1)
    (acquirePreparedCacheBase_spec C c p witness rest a hc hin hW hcap hempty)
    fun b ⟨hbi, hbl, hbr, hbcursor, hbo, hbsh, hbc, hbfr⟩ => ?_
  refine (hs_copy C preparedLength StageMain.Compact.compactLength b (by decide)).mono le_rfl ?_
  rintro d rfl
  have hf : Fr a (b.set preparedLength (b.env StageMain.Compact.compactLength))
      (preparedLength :: StageMain.Compact.acquireScratch) :=
    (hbfr.weaken (by intro x hx; simp only [List.mem_cons]; tauto)).trans (Fr.set _ _ (by simp))
  exact ⟨hbi, hbl, hbr, hbcursor, hbo, hbsh, Cst.of_fr hc hf (by decide), hf⟩

end NearQuarticWires.StageLift
