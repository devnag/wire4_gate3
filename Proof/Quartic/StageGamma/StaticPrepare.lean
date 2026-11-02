import Proof.Quartic.StageGamma.CellsPrepare
import Proof.Quartic.StageGamma.Census

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: every
ORIGINAL request field and its cached modulus survive static preparation. -/
def staticScratch : List (Fin VV) :=
  [gammaRest, gammaCellWidth, gammaSide, gammaPowerIndex, gammaBase, gammaCensus,
    gammaProductTemp] ++ (List.finRange 8).map gammaCell ++ [vJ]

/-- `cor:conditional`, paper/paper.tex: the static
workspace is disjoint from all ORIGINAL request and cached-field variables. -/
theorem staticScratch_header :
    (∀ i : Fin 14, requestFieldRegister i ∉ staticScratch) ∧ gammaModulus ∉ staticScratch := by
  constructor
  · intro i
    fin_cases i <;> decide
  · decide

/-- `cor:conditional`, paper/paper.tex: preserving
the exact header variables and source frame preserves the decoded request. -/
theorem CachedHeader.preserve (request : Machine.GammaRequest) {a b : DS VV MM}
    (ha : CachedHeader request a) (hs : Same a b) (hc : Cst b)
    (hf : Fr a b staticScratch) : CachedHeader request b := by
  refine ⟨?_, ?_, hs.ip.trans ha.2.2.1, hs.kin.trans ha.2.2.2.1, hc⟩
  · intro i
    rw [hf _ (staticScratch_header.1 i)]
    exact ha.1 i
  · rw [hf _ staticScratch_header.2]
    exact ha.2.1

/-- `cor:conditional`, paper/paper.tex: literal
decoded header fields give the parameters used by actual binary setup. -/
theorem CachedHeader.fields (request : Machine.GammaRequest) (a : DS VV MM)
    (ha : CachedHeader request a) :
    a.env (requestFieldRegister 0) = request.parameters.ell ∧
    a.env (requestFieldRegister 1) = request.parameters.kh ∧
    a.env (requestFieldRegister 2) = request.parameters.Q ∧
    a.env (requestFieldRegister 3) = request.prefixLength ∧
    a.env (requestFieldRegister 4) = request.prefixCode ∧
    a.env (requestFieldRegister 5) = 8 := by
  exact ⟨by simpa [requestFields] using ha.1 0,
    by simpa [requestFields] using ha.1 1,
    by simpa [requestFields] using ha.1 2,
    by simpa [requestFields] using ha.1 3,
    by simpa [requestFields] using ha.1 4,
    by simpa [requestFields] using ha.1 5⟩

/-- `cor:conditional`, paper/paper.tex: every
original walk vertex comes from the exact fourteen-field request parser. -/
theorem CachedHeader.vertices (request : Machine.GammaRequest) (a : DS VV MM)
    (ha : CachedHeader request a) :
    ∀ slot, a.env (gammaVertex slot) = (request.walk slot).val := by
  intro slot
  have hh := ha.1 ⟨slot.val + 6, by have := slot.isLt; omega⟩
  fin_cases slot <;> simpa [requestFields, gammaVertex, requestFieldRegister] using hh

/-- `cor:conditional`, paper/paper.tex: the complete
choice-independent state contains only data physically derived from the
ORIGINAL request and its once-computed field cache. -/
structure StaticReady (request : Machine.GammaRequest) (a : DS VV MM) : Prop where
  header : CachedHeader request a
  rest : a.env gammaRest = Cycle.seedLength request.parameters - request.prefixLength
  cellWidth : a.env gammaCellWidth = 2 * request.parameters.kh
  side : a.env gammaSide = request.parameters.N
  cells : ∀ slot, a.env (gammaCell slot) =
    NearCubicWires.WireExponent3_5.Sampler.cellNum request.parameters
      (Cycle.edge (by norm_num) request.walk slot)
  base : a.env gammaBase = request.parameters.Q + 1
  census : a.env gammaCensus = (request.parameters.Q + 1) ^ 8

/-- `cor:conditional`, paper/paper.tex: finite
physical static preparation computes widths, side length, all original
walk cells and the exact coefficient census once before enumeration. -/
def staticPrepare : St VV MM :=
  .seq prepareWidths (.seq prepareSide (.seq prepareCells prepareCensus))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the whole choice-independent physical state is produced
from the decoded ORIGINAL header in polynomial seed time. -/
theorem staticPrepare_run (C : Ctx) (request : Machine.GammaRequest)
    (a : DS VV MM) (ha : CachedHeader request a)
    (hwidth : Cycle.seedLength request.parameters + 10 ≤ C.Wd) :
    Hs C staticPrepare a (5 * request.parameters.kh + 121) (fun b =>
      StaticReady request b ∧ Same a b ∧ Fr a b staticScratch) := by
  have hell := (CachedHeader.fields request a ha).1
  have hkh := (CachedHeader.fields request a ha).2.1
  have hplen := (CachedHeader.fields request a ha).2.2.2.1
  have hkseed : 2 * request.parameters.kh ≤ Cycle.seedLength request.parameters := by
    have hh := request.parameters.k_le
    dsimp [Cycle.seedLength]
    omega
  unfold staticPrepare
  refine Hs.mono (Hs.seq (t1 := 13) (t2 := 5 * request.parameters.kh + 107)
    (prepareWidths_run C request a ha.2.2.2.2 hell hkh hplen (by omega)) ?_)
    (by omega) (fun _ h => h)
  intro b ⟨br, bk, bs, bc, bf⟩
  have bf' : Fr a b staticScratch := bf.weaken (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [staticScratch])
  have bh := CachedHeader.preserve request ha bs bc bf'
  refine Hs.seq (t1 := 5 * request.parameters.kh + 6) (t2 := 100)
    (prepareSide_run C request b bc (CachedHeader.fields request b bh).2.1 (by omega)) ?_
  intro d ⟨dside, ds, dc, df⟩
  have df' : Fr b d staticScratch := df.weaken (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [staticScratch])
  have dh := CachedHeader.preserve request bh ds dc df'
  refine Hs.seq (t1 := 33) (t2 := 66)
    (prepareCells_run C request d dc (by omega) dside (CachedHeader.vertices request d dh)) ?_
  intro e ⟨ecells, es, ec, ef⟩
  have ef' : Fr d e staticScratch := ef.weaken (by
    intro x hx
    simpa only [staticScratch, List.append_assoc] using
      (List.mem_append_right
        [gammaRest, gammaCellWidth, gammaSide, gammaPowerIndex, gammaBase, gammaCensus,
          gammaProductTemp] hx))
  have eh := CachedHeader.preserve request dh es ec ef'
  have efields := CachedHeader.fields request e eh
  refine Hs.mono (prepareCensus_run C request e ec efields.2.2.1 efields.2.2.2.2.2 hwidth) le_rfl ?_
  intro f ⟨fbase, fcensus, fs, fc, ff⟩
  have ff' : Fr e f staticScratch := ff.weaken (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [staticScratch])
  refine ⟨⟨CachedHeader.preserve request eh fs fc ff', ?_, ?_, ?_, ?_, fbase, fcensus⟩,
    bs.trans (ds.trans (es.trans fs)), bf'.trans (df'.trans (ef'.trans ff'))⟩
  · rw [ff gammaRest (by decide), ef gammaRest (by decide), df gammaRest (by decide)]
    exact br
  · rw [ff gammaCellWidth (by decide), ef gammaCellWidth (by decide), df gammaCellWidth (by decide)]
    exact bk
  · rw [ff gammaSide (by decide), ef gammaSide (by decide)]
    exact dside
  · intro slot
    rw [ff (gammaCell slot) (by fin_cases slot <;> decide)]
    exact ecells slot

end NearQuarticWires.StageGamma
