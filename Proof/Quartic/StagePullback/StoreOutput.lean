import Proof.Quartic.StagePullback.NativeCounts
import Proof.Quartic.StagePullback.Padding

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.NativeRows

open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells

def selectedStore (isLeft : Bool) : Fin MM := if isLeft then leftStore else rightStore
def selectedCount (isLeft : Bool) : Fin VV := if isLeft then leftCount else rightCount
def outputScratch : List (Fin VV) := SignedCoefficients.value :: outputIndex :: FieldOutput.scratch

/-- `lem:print`, paper/paper.tex: read an actual
native signed record while available and physically supply zero in its
canonical padding positions. -/
def readPadded (isLeft : Bool) : St VV MM :=
  .ite (.lt outputIndex (selectedCount isLeft))
    (.op (.rdM (selectedStore isLeft) SignedCoefficients.value))
    (.op (.zero SignedCoefficients.value))

/-- `lem:print` and `prop:time`, paper/paper.tex: actual stored records and zero padding are produced by
one paid read or zero operation with the exact physical store cursor. -/
theorem readPadded_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (isLeft : Bool)
    (xs : List ℕ) (k : ℕ) (hram : a.ram (selectedStore isLeft) = xs)
    (hrc : a.rc (selectedStore isLeft) = min k xs.length)
    (hk : a.env outputIndex = k) (hcount : a.env (selectedCount isLeft) = xs.length) :
    Hs C (readPadded isLeft) a 2 (fun b =>
      b.env SignedCoefficients.value = xs.getD k 0 ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc (selectedStore isLeft) (min (k + 1) xs.length) ∧
      Cst b ∧ Fr a b [SignedCoefficients.value]) := by
  have hne : outputIndex ≠ selectedCount isLeft := by cases isLeft <;> decide
  unfold readPadded
  by_cases hlen : k < xs.length
  · have he : a.rc (selectedStore isLeft) < (a.ram (selectedStore isLeft)).length := by
      rw [hrc, hram, Nat.min_eq_left hlen.le]
      exact hlen
    refine Hs.mono (Hs.iteT hne (by simp [Cnd.eval, hk, hcount, hlen])
      (hs_rdM C (selectedStore isLeft) SignedCoefficients.value a he)) le_rfl ?_
    rintro b rfl
    have hf : Fr a ((a.set SignedCoefficients.value
        ((a.ram (selectedStore isLeft)).getD (a.rc (selectedStore isLeft)) 0)).adv
          (selectedStore isLeft)) [SignedCoefficients.value] := Fr.set a _ (by simp)
    refine ⟨by simp only [DS.adv, DS.set_env_self, hram, hrc, Nat.min_eq_left hlen.le],
      rfl, rfl, rfl, ?_, ?_, hf⟩
    · simp only [DS.adv, DS.set_rc, hrc, Nat.min_eq_left hlen.le,
        Nat.min_eq_left (show k + 1 ≤ xs.length by omega)]
    · exact ⟨by rw [hf _ (by decide)]; exact hc.z,
        by rw [hf _ (by decide)]; exact hc.one, by rw [hf _ (by decide)]; exact hc.two⟩
  · refine Hs.mono (Hs.iteF hne (by simp [Cnd.eval, hk, hcount, hlen])
      (hs_zero C SignedCoefficients.value a)) le_rfl ?_
    rintro b rfl
    have hf : Fr a (a.set SignedCoefficients.value 0) [SignedCoefficients.value] := Fr.set a _ (by simp)
    refine ⟨by rw [DS.set_env_self, List.getD_eq_default xs 0 (by omega)], rfl, rfl, rfl, ?_,
      hc.of_fr hf (by decide), hf⟩
    funext m
    by_cases hm : m = selectedStore isLeft
    · subst hm
      simp only [Function.update_self, DS.set_rc, hrc, Nat.min_eq_right (by omega : xs.length ≤ k),
        Nat.min_eq_right (by omega : xs.length ≤ k + 1)]
    · exact (Function.update_of_ne hm _ _).symm

/-- `lem:print`, paper/paper.tex: rewind the real
native side store and write its entire common-width signed row. -/
def storeProgram (isLeft : Bool) : St VV MM :=
  .seq (.op (.rwM (selectedStore isLeft)))
    (forS outputIndex nativeWidth (.seq (readPadded isLeft) FieldOutput.program))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual native signed store is serialized with exact
zero padding, while retaining the original input cursor and both stores. -/
theorem storeProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (isLeft : Bool)
    (xs : List ℕ) (W L : ℕ) (hram : a.ram (selectedStore isLeft) = xs)
    (hrc : a.rc (selectedStore isLeft) = xs.length)
    (hcount : a.env (selectedCount isLeft) = xs.length)
    (hwidth : a.env nativeWidth = W) (hfield : a.env FieldOutput.width = L)
    (hlen : xs.length ≤ W) (hW : W < 2 ^ C.Wd) (hL : L < 2 ^ C.Wd) (hWd : 2 ≤ C.Wd) :
    Hs C (storeProgram isLeft) a (xs.length + W * (12 * L + 16) + 10) (fun b =>
      b.out = a.out ++ (padNumbers W xs).flatMap (fun v => frame (binary L v)) ∧
      b.ip = a.ip ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ Cst b ∧ Fr a b outputScratch) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.out = a.out ++ (List.range k).flatMap (fun i => frame (binary L (xs.getD i 0))) ∧
    b.ip = a.ip ∧ b.ram = a.ram ∧
    b.rc = Function.update a.rc (selectedStore isLeft) (min k xs.length) ∧
    Cst b ∧ Fr a b outputScratch
  have hI : ∀ k b val, I k b → I k (b.set outputIndex val) := by
    rintro k b val ⟨hout, hip, hram, hrc, hbc, hfr⟩
    exact ⟨hout, hip, hram, hrc,
      hbc.of_fr (T := outputScratch) (Fr.set b _ (by simp [outputScratch])) (by decide),
      hfr.trans (Fr.set b _ (by simp [outputScratch]))⟩
  have hbody : ∀ k < W, ∀ b, I k b → b.env outputIndex = k → b.env nativeWidth = W →
      Hs C (.seq (readPadded isLeft) FieldOutput.program) b (12 * L + 12)
        (fun d => I (k + 1) d ∧ d.env outputIndex = k ∧ d.env nativeWidth = W) := by
    rintro k hk b ⟨hout, hip, hbram, hbrc, hbc, hbfr⟩ hki hcn
    have hbcnt : b.env (selectedCount isLeft) = xs.length :=
      (hbfr _ (by cases isLeft <;> decide)).trans hcount
    have hbfld : b.env FieldOutput.width = L := (hbfr _ (by decide)).trans hfield
    refine Hs.mono (Hs.seq (t1 := 2) (t2 := 12 * L + 8)
      (readPadded_run C b hbc isLeft xs k (by rw [hbram, hram])
        (by rw [hbrc, Function.update_self]) hki hbcnt)
      (fun c ⟨hcv, hcip, hcout, hcram, hcrc, hcc, hcfr⟩ => ?_)) (by omega) (fun _ h => h)
    have hcfld : c.env FieldOutput.width = L := (hcfr _ (by decide)).trans hbfld
    refine Hs.mono (FieldOutput.program_run C c hcc L (xs.getD k 0) hcfld hcv hL hWd) le_rfl ?_
    rintro d ⟨hdout, hdrest, hdc, hdfr⟩
    have hdip : d.ip = c.ip := congrArg Prod.fst hdrest
    have hdram : d.ram = c.ram := congrArg (fun v => v.2.1) hdrest
    have hdrc : d.rc = c.rc := congrArg (fun v => v.2.2.1) hdrest
    have hca : Fr b c outputScratch := hcfr.weaken (by
      intro y hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact List.mem_cons_self ..)
    have hda : Fr c d outputScratch := hdfr.weaken (by
      intro y hy
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))
    refine ⟨⟨?_, hdip.trans (hcip.trans hip), hdram.trans (hcram.trans hbram), ?_, hdc,
      hbfr.trans (hca.trans hda)⟩,
      (hdfr _ (by decide)).trans ((hcfr _ (by decide)).trans hki),
      (hdfr _ (by decide)).trans ((hcfr _ (by decide)).trans hcn)⟩
    · rw [hdout, hcout, hout, List.range_succ]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    · rw [hdrc, hcrc, hbrc, Function.update_idem]
  unfold storeProgram
  refine Hs.mono (Hs.seq (t1 := a.rc (selectedStore isLeft) + 1)
    (t2 := W * (12 * L + 16) + 4) (hs_rwM C (selectedStore isLeft) a) (fun b hb => ?_))
    (by rw [hrc]; omega) (fun _ h => h)
  subst hb
  let b := a.rew (selectedStore isLeft)
  have h0 : I 0 b := ⟨by simp [b, DS.rew], rfl, rfl, by simp [b, DS.rew],
    ⟨hc.z, hc.one, hc.two⟩, fun _ _ => rfl⟩
  have hbn : b.env nativeWidth = W := hwidth
  refine Hs.mono (forS_spec' outputIndex nativeWidth (by decide)
    (.seq (readPadded isLeft) FieldOutput.program) b W hW I (12 * L + 12) hI h0 hbn hbody)
    (by rw [show 12 * L + 12 + 4 = 12 * L + 16 by omega]) ?_
  rintro c ⟨⟨hout, hip, hcram, hcrc, hcc, hcfr⟩, _, _⟩
  refine ⟨?_, hip, hcram, ?_, hcc, hcfr⟩
  · rw [indexed_records_pad L W xs hlen] at hout
    exact hout
  · rw [hcrc, Nat.min_eq_right hlen, ← hrc]
    exact Function.update_eq_self ..

end NearQuarticWires.StagePullback.NativeRows
