import Proof.Quartic.StageRecovery.TermRecords

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: retaining every
record store and physical head retains the exact term-stream alignment. -/
theorem TermStreamAt.of_rest {records : List (ℕ × ℕ)} {k : ℕ} {a b : DS VV MM}
    (h : TermStreamAt records k a) (hr : supportPrintRest b = supportPrintRest a) :
    TermStreamAt records k b := by
  have hm : b.ram = a.ram := congrArg (fun x => x.2.1) hr
  have hc : b.rc = a.rc := congrArg (fun x => x.2.2.1) hr
  exact ⟨by rw [hm]; exact h.supports, by rw [hm]; exact h.coefficients,
    by rw [hc]; exact h.supportCursor, by rw [hc]; exact h.coefficientCursor⟩

/-- `lem:print`, paper/paper.tex: the entire canonical
Terms word is emitted by one paid list header and one finite sequential
loop over the original support and computed coefficient records. -/
def emitTermsProgram : St VV MM :=
  .seq (emitVariable cacheCountVar) (forS outerIndexVar cacheCountVar emitTermStep)

/-- `prop:time`, paper/paper.tex: canonical output
has a linear record-count clock with a fixed polynomial per-term factor. -/
def termsCodecCost (V q N : ℕ) : ℕ :=
  (40 * natBitLength N + 42) + (N * (monomialCost V q + 8) + 4) + 1

/-- `lem:print`, paper/paper.tex: the actual writer
emits the literal canonical Terms word without supplied serialized
output, random record access or observation of a callee's output length. -/
theorem emitTermsProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (V q : ℕ) (records : List (ℕ × ℕ)) (ha : TermStreamAt records 0 a)
    (hV : a.env arityVar = V) (hcount : a.env cacheCountVar = records.length)
    (hvalues : ∀ p ∈ records, p.2 < q) (hW : 2 ≤ C.Wd)
    (hVfit : V + 3 < 2 ^ C.Wd) (hzero : natBitLength 0 + 2 < 2 ^ C.Wd)
    (hqfit : natBitLength q + 2 < 2 ^ C.Wd)
    (hNfit : records.length < 2 ^ C.Wd)
    (hNcodec : natBitLength records.length + 2 < 2 ^ C.Wd) :
    Hs C emitTermsProgram a (termsCodecCost V q records.length) (fun b =>
      b.out = a.out ++ termsWord (termsOfRecords V records) ∧ Cst b) := by
  let termWord := fun p : ℕ × ℕ => monoWord (setOf V p.1, (p.2 : ℤ))
  let I : ℕ → DS VV MM → Prop := fun k b =>
    TermStreamAt records k b ∧
    b.out = a.out ++ natWord records.length ++ (records.take k).flatMap termWord ∧
    Cst b ∧ Fr a b (outerIndexVar :: emitTermScratch)
  unfold emitTermsProgram termsCodecCost
  refine Hs.seq (t2 := records.length * (monomialCost V q + 8) + 4)
    ((emitVariable_spec C a hc cacheCountVar (by decide) hW (by rw [hcount]; exact hNcodec)).mono
      (by rw [hcount]) (fun _ h => h))
    fun b ⟨hbo, hbr, hbc, hbf⟩ => ?_
  have hstart := ha.of_rest hbr
  refine (forS_spec' (C := C) outerIndexVar cacheCountVar (by decide) emitTermStep b
    records.length hNfit I (monomialCost V q + 4) ?_
    ⟨hstart, by simpa only [List.take_zero, List.flatMap_nil, List.append_nil, hcount] using hbo,
      hbc, Fr.weaken hbf (by decide)⟩
    (by rw [hbf _ (by decide), hcount]) ?_).mono (by simp) ?_
  · intro k b value ⟨hs, ho, hbc, hbf⟩
    exact ⟨hs.set _ _, ho,
      Cst.of_fr (T := [outerIndexVar]) hbc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans hbf (Fr.set _ _ (by simp))⟩
  · intro k hk b ⟨hs, ho, hbc, hbf⟩ hbi hbn
    refine (emitTermStep_spec C b hbc V q records k hk hs
      (by rw [hbf _ (by decide), hV]) hvalues hW hVfit hzero hqfit).mono le_rfl ?_
    rintro d ⟨hds, hdo, hdc, hdf⟩
    refine ⟨⟨hds, ?_, hdc,
      Fr.trans hbf (Fr.weaken hdf (by intro x hx; exact List.mem_cons_of_mem _ hx))⟩,
      by rw [hdf _ (by decide), hbi], by rw [hdf _ (by decide), hbn]⟩
    rw [hdo, ho, List.take_succ_eq_append_getElem hk, List.flatMap_append,
      List.flatMap_singleton, List.append_assoc]
  · rintro b ⟨⟨_, ho, hbc, _⟩, _, _⟩
    refine ⟨?_, hbc⟩
    simpa only [termsWord, listWord, termsOfRecords, List.length_map,
      List.flatMap_map, Function.comp_def, List.take_length, termWord, List.append_assoc] using ho

end NearQuarticWires.StageRecovery
