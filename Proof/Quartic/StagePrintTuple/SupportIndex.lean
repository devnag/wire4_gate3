import Proof.Quartic.StagePrintTuple.NaturalPrefix
import Proof.Quartic.StagePrint.RawInitialization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StageTuple

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: an actual
cached support and a valid finite reverse-iteration position determine
one original formula-variable codec, preserving repeated values if present. -/
structure SupportIndexRequest where
  support : List ℕ
  index : Fin support.length

/-- `lem:print`, paper/paper.tex: the selected
position and the complete small support cache are physically serialized. -/
def SupportIndexRequest.word (r : SupportIndexRequest) : List Bool :=
  natWord r.index.val ++ listWord natWord r.support

/-- `lem:print`, paper/paper.tex: the selected
variable keeps its exact canonical natural-number source codec. -/
def SupportIndexRequest.output (r : SupportIndexRequest) : List Bool :=
  natWord r.support[r.index.val]

/-- `lem:print`, paper/paper.tex: the actual
binary support reader initializes constants, reads both real counts,
scans precisely the preceding variable codecs and prints the selected one. -/
def supportIndexProgram : St VV :=
  .seq StagePrint.RawBits.initializeConstants
    (.seq readNat (.seq (.op (.copy oJ t3)) (.seq readNat
      (.seq naturalPrefixProgram (.seq readNat emitNat)))))

/-- `prop:time`, paper/paper.tex: one support
selection pays its actual prefix scan and binary parsing/printing work;
the complete Terms source is never part of this arithmetic input. -/
def SupportIndexRequest.steps (C : Ctx) (r : SupportIndexRequest) : ℕ :=
  r.index.val * (30 * C.Wd + 64) + 200 * C.Wd + 400

/-- `lem:print`, paper/paper.tex: every natural
codec in the actual support has its own bounded literal source span. -/
theorem naturalWord_member_length (support : List ℕ) (v : ℕ) (hv : v ∈ support) :
    (natWord v).length ≤ (support.flatMap natWord).length := by
  induction support with
  | nil => simp at hv
  | cons w support ih =>
    rcases List.mem_cons.mp hv with he | ht
    · subst w
      simp only [List.flatMap_cons, List.length_append]
      omega
    · exact (ih ht).trans (by simp)

/-- `lem:print`, paper/paper.tex: the support
count is bounded by its actual canonical source bytes, including zero values. -/
theorem naturalCount_le_word (support : List ℕ) :
    support.length ≤ (support.flatMap natWord).length := by
  induction support with
  | nil => simp
  | cons v support ih =>
    have hp : 1 ≤ (natWord v).length := by rw [natWord_length]; omega
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

/-- `lem:print` and `prop:time`, paper/paper.tex: actual finite support selection starts cold and returns
exactly the chosen source variable, without a decoded variable oracle. -/
theorem supportIndexProgram_run (C : Ctx) (r : SupportIndexRequest)
    (hcw : C.cw = r.word) (hW : C.cw.length + 3 ≤ C.Wd) :
    Hs C supportIndexProgram (a0 (V := VV)) (r.steps C) (fun b => b.out = r.output) := by
  have hctx : 3 ≤ C.Wd := by omega
  have hL : C.cw.length + 2 < 2 ^ C.Wd :=
    lt_of_lt_of_le (by omega : C.cw.length + 2 < C.Wd) (Nat.lt_two_pow_self.le)
  have hflat : (r.support.flatMap natWord).length ≤ C.cw.length := by
    rw [hcw, SupportIndexRequest.word, listWord, List.length_append, List.length_append]
    omega
  have hcount : r.support.length < 2 ^ C.Wd :=
    ((naturalCount_le_word r.support).trans hflat).trans_lt
      (lt_of_lt_of_le (by omega : C.cw.length < C.Wd) (Nat.lt_two_pow_self.le))
  have hvars : ∀ v ∈ r.support, natBitLength v + 2 ≤ C.Wd := by
    intro v hv
    have hw := naturalWord_member_length r.support v hv
    have hb := natBitLength_le_len v
    omega
  have hib : natBitLength r.index.val + 2 ≤ C.Wd := by
    have hi := natBitLength_le_len r.index.val
    have hl : (natWord r.index.val).length ≤ C.cw.length := by
      rw [hcw, SupportIndexRequest.word, List.length_append]
      omega
    omega
  have hnb : natBitLength r.support.length + 2 ≤ C.Wd := by
    have hi := natBitLength_le_len r.support.length
    have hl : (natWord r.support.length).length ≤ C.cw.length := by
      rw [hcw, SupportIndexRequest.word, listWord, List.length_append, List.length_append]
      omega
    omega
  unfold supportIndexProgram
  refine Hx.hs (Hs.then (StagePrint.RawBits.initialize_run C hctx)
    (fun a ⟨ac, ap, _, ao, _⟩ n1 hn1 => ?_))
  have hd : C.cw.drop a.cp = natWord r.index.val ++ listWord natWord r.support := by
    rw [ap, List.drop_zero, hcw]
    rfl
  refine Hs.then (readNat_spec a ac r.index.val _ hd hib hL)
    (fun b ⟨bv, _, bp, _, bo, bc, _⟩ n2 hn2 => ?_)
  refine Hs.then (hs_copy C oJ t3 b (by decide)) (fun e he n3 hn3 => ?_)
  subst he
  let e := b.set oJ (b.env t3)
  have ef : Fr b e [oJ] := Fr.set _ _ (by simp)
  have ec : Cst e := Cst.of_fr bc ef (by decide)
    (by rw [ef vPOS (by decide)]; exact bc.pos)
  have ed : C.cw.drop e.cp = natWord r.support.length ++ r.support.flatMap natWord := by
    change C.cw.drop b.cp = _
    rw [bp, ← List.drop_drop, hd, List.drop_left]
    rfl
  refine Hs.then (readNat_spec e ec r.support.length _ ed hnb hL)
    (fun f ⟨_, _, fp, _, fo, fc, ff⟩ n4 hn4 => ?_)
  have fd : C.cw.drop f.cp = r.support.flatMap natWord ++ [] := by
    rw [fp, ← List.drop_drop, ed, List.drop_left, List.append_nil]
  have fj : f.env oJ = r.index.val := by rw [ff oJ (by decide)]; simp [e, bv]
  refine Hs.then (naturalPrefixProgram_run C r.support r.index.val [] f fc
    (by omega) fj fd hvars hL hcount)
    (fun g ⟨gd, gc, _, go, _⟩ n5 hn5 => ?_)
  have gd' : C.cw.drop g.cp = natWord r.support[r.index.val] ++
      (r.support.drop (r.index.val + 1)).flatMap natWord := by
    rw [gd, List.append_nil, List.drop_eq_getElem_cons r.index.isLt, List.flatMap_cons]
  refine Hs.then (readNat_spec g gc r.support[r.index.val] _ gd'
    (hvars _ (List.getElem_mem r.index.isLt)) hL)
    (fun h ⟨hv, _, _, _, ho, hc, _⟩ n6 hn6 => ?_)
  have hval : natBitLength (h.env t3) + 2 < 2 ^ C.Wd := by
    rw [hv]
    exact (hvars _ (List.getElem_mem r.index.isLt)).trans_lt Nat.lt_two_pow_self
  refine Hs.last (emitNat_spec h hc (by omega) hval)
    (fun k ⟨ko, _, _, _, _⟩ n7 hn7 => ?_)
  refine ⟨?_, ?_⟩
  · rw [ko, ho, go, fo]
    simp [SupportIndexRequest.output, e, bo, ao, hv]
  · unfold SupportIndexRequest.steps
    have hselected := hvars _ (List.getElem_mem r.index.isLt)
    rw [hv] at hn7
    omega

end NearQuarticWires.StageTuple
