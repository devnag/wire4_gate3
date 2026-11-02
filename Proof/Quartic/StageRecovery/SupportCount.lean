import Proof.Quartic.StageRecovery.SupportCodec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells NearCubicGates.Close.Expand

/-- `lem:print`, paper/paper.tex: the cardinality
pass uses only its binary suffix, bit and count work registers. -/
def supportCountScratch : List (Fin VV) :=
  [supportWork, supportQuotient, supportBit, supportDegree, vJ, supportIndex]

/-- `lem:print`, paper/paper.tex: a real first pass
computes the support-list length before any monomial bytes are emitted. -/
def countSupportProgram : St VV MM :=
  .seq (.op (.zero supportDegree))
    (.seq (.op (.copy supportWork supportVar))
      (forS supportIndex arityVar supportCountStep))

/-- `lem:print`, paper/paper.tex: the canonical
monomial count is computed from its actual characteristic support,
using a finite linear scan and retaining every physical tape. -/
theorem countSupportProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (V s : ℕ) (hV : a.env arityVar = V) (hs : a.env supportVar = s)
    (hVfit : V < 2 ^ C.Wd) (hfour : 4 ≤ 2 ^ C.Wd) :
    Hs C countSupportProgram a (10 * V + 8) (fun b =>
      b.env supportDegree = (setOf V s).card ∧ b.sh = a.sh ∧ Cst b ∧
        Fr a b supportCountScratch) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env supportWork = s / 2 ^ k ∧ b.env supportDegree = (supportIndices s k).length ∧
    b.sh = a.sh ∧ Cst b ∧ Fr a b supportCountScratch
  unfold countSupportProgram
  refine (Hs.seq (t2 := 10 * V + 6) (hs_zero C supportDegree a) fun b hb => ?_).mono
    (by omega) (fun _ h => h)
  subst b
  refine (Hs.seq (t2 := 10 * V + 4) (hs_copy C supportWork supportVar _ (by decide))
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let start := (a.set supportDegree 0).set supportWork s
  have heq : (a.set supportDegree 0).set supportWork ((a.set supportDegree 0).env supportVar) = start := by
    simp (config := {decide := true}) [start, DS.set, hs]
  rw [heq]
  have hstart : Fr a start supportCountScratch :=
    Fr.trans (Fr.set _ _ (by simp [supportCountScratch])) (Fr.set _ _ (by simp [supportCountScratch]))
  have hstartc : Cst start := Cst.of_fr hc hstart (by decide)
  refine (forS_spec' (C := C) supportIndex arityVar (by decide) supportCountStep start V hVfit I 6
    ?_ ⟨by simp [start, DS.set], by simp (config := {decide := true}) [start, DS.set, supportIndices],
      rfl, hstartc, hstart⟩
    (by rw [hstart _ (by decide), hV]) ?_).mono (by omega) ?_
  · intro k b value ⟨hw, hd, hsh, hbc, hbf⟩
    refine ⟨by simpa (config := {decide := true}) only [DS.set_env_ne] using hw,
      by simpa (config := {decide := true}) only [DS.set_env_ne] using hd, hsh,
      Cst.of_fr (T := [supportIndex]) hbc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans hbf (Fr.set _ _ (by simp [supportCountScratch]))⟩
  · intro k hk b ⟨hw, hd, hsh, hbc, hbf⟩ hbi hbn
    refine (supportCountStep_spec C b hbc s k hw hd (by omega) hfour).mono le_rfl ?_
    rintro d ⟨hdw, hdd, hdsh, hdc, hdf⟩
    exact ⟨⟨hdw, hdd, hdsh.trans hsh, hdc,
      Fr.trans hbf (Fr.weaken hdf (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        simp only [supportCountScratch, List.mem_cons, List.not_mem_nil, or_false]
        tauto))⟩,
      by rw [hdf _ (by decide), hbi], by rw [hdf _ (by decide), hbn]⟩
  · rintro b ⟨⟨_, hd, hsh, hbc, hbf⟩, _, _⟩
    exact ⟨hd.trans (supportIndices_length V s), hsh, hbc, hbf⟩

end NearQuarticWires.StageRecovery
