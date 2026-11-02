import Proof.Quartic.StageLift.PreparedCache

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells

private theorem permuteMemory_inverse {V M : ℕ} (e : Fin M ≃ Fin M) (a : DS V M) :
    permuteMemory e (permuteMemory e.symm a) = a := by
  cases a
  simp only [permuteMemory, Equiv.symm_symm, Equiv.apply_symm_apply]

/-- Step 3 and `lem:print`, paper/paper.tex: repeated source queries reuse the actual compact
source emitter with its finite source store relabeled to9. -/
def emitPreparedCacheBase : St VV MM :=
  permuteProgram preparedPermutation StageMain.Compact.emitCompact

/-- Step 3 and `lem:print`, paper/paper.tex: every actual compact-source bit is written to the
callee request with its original paid rewind and copy cost. -/
theorem emitPreparedCacheBase_spec (C : Ctx) (bits : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hbits : a.ram preparedStore = bits.map Bool.toNat)
    (hlen : a.env StageMain.Compact.compactLength = bits.length)
    (hfit : bits.length < 2 ^ C.Wd) (hroom : a.kin.length + bits.length ≤ C.Lk) :
    Hs C emitPreparedCacheBase a (a.rc preparedStore + 8 * bits.length + 6) (fun b =>
      b.kin = a.kin ++ bits ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc preparedStore bits.length ∧
      b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧ Fr a b [c0, t0]) := by
  let old := permuteMemory preparedPermutation.symm a
  have hold : Cst old := ⟨hc.z, hc.one, hc.two⟩
  have hbits0 : old.ram StageMain.Compact.compactStore = bits.map Bool.toNat := by
    simpa only [old, permuteMemory, preparedPermutation, Equiv.symm_symm,
      Equiv.swap_apply_left] using hbits
  obtain ⟨b, n, he, hn, hbkin, hbip, hbo, hbram, hbrc, hbkout, hbkc, hbc, hbfr⟩ :=
    StageMain.Compact.emitCompact_run C bits old hold hbits0 hlen hfit hroom
  have hex : Ex C emitPreparedCacheBase a (permuteMemory preparedPermutation b) n := by
    simpa only [emitPreparedCacheBase, old, permuteMemory_inverse] using
      execution_permuteMemory preparedPermutation he
  have hcursor : old.rc StageMain.Compact.compactStore = a.rc preparedStore := by
    simp only [old, permuteMemory, preparedPermutation, Equiv.symm_symm, Equiv.swap_apply_left]
  rw [hcursor] at hn
  refine ⟨permuteMemory preparedPermutation b, n, hex, hn, hbkin, hbip, hbo, ?_, ?_, hbkout, hbkc,
    ⟨hbc.z, hbc.one, hbc.two⟩, ?_⟩
  · funext store
    change b.ram (preparedPermutation.symm store) = a.ram store
    rw [hbram]
    simp only [old, permuteMemory, Equiv.symm_symm, Equiv.apply_symm_apply]
  · funext store
    change b.rc (preparedPermutation.symm store) = Function.update a.rc preparedStore bits.length store
    rw [hbrc]
    have hrc0 : (fun i => old.rc (preparedPermutation.symm i)) = a.rc := by
      funext i
      simp only [old, permuteMemory, Equiv.symm_symm, Equiv.apply_symm_apply]
    have hupdate := congrFun (permute_update preparedPermutation old.rc
      StageMain.Compact.compactStore bits.length) store
    rw [hrc0] at hupdate
    simpa only [preparedPermutation, Equiv.swap_apply_left] using hupdate
  · intro x hx
    exact hbfr x hx

/-- Step 3 and `lem:print`, paper/paper.tex: the measured source length is reloaded from its
persistent field after any intervening mask or binomial computation. -/
def emitPreparedCache : St VV MM :=
  .seq (.op (.copy StageMain.Compact.compactLength preparedLength)) emitPreparedCacheBase

/-- Step 3 and `lem:print`, paper/paper.tex: the actual prepared source supplies repeated small
callee requests without crossing or copying the original Gamma table. -/
theorem emitPreparedCache_spec (C : Ctx) (bits : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hbits : a.ram preparedStore = bits.map Bool.toNat)
    (hlen : a.env preparedLength = bits.length)
    (hfit : bits.length < 2 ^ C.Wd) (hroom : a.kin.length + bits.length ≤ C.Lk) :
    Hs C emitPreparedCache a (a.rc preparedStore + 8 * bits.length + 8) (fun b =>
      b.kin = a.kin ++ bits ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc preparedStore bits.length ∧
      b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧
      Fr a b [StageMain.Compact.compactLength, c0, t0]) := by
  unfold emitPreparedCache
  refine (Hs.seq (t2 := a.rc preparedStore + 8 * bits.length + 6)
    (hs_copy C StageMain.Compact.compactLength preparedLength a (by decide))
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let b := a.set StageMain.Compact.compactLength (a.env preparedLength)
  have hbc : Cst b := Cst.of_fr (T := [StageMain.Compact.compactLength]) hc
    (Fr.set a _ (by simp)) (by decide)
  refine (emitPreparedCacheBase_spec C bits b hbc hbits hlen hfit hroom).mono le_rfl ?_
  rintro d ⟨hdkin, hdip, hdo, hdram, hdrc, hdkout, hdkc, hdc, hdfr⟩
  refine ⟨hdkin, hdip, hdo, hdram, hdrc, hdkout, hdkc, hdc, ?_⟩
  exact (Fr.set a _ (by simp)).trans (hdfr.weaken (by simp))

end NearQuarticWires.StageLift
