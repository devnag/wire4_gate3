import Proof.Quartic.StageMainMask.EntryHeader
import Proof.Quartic.StageMainMask.EntryDecode
import Proof.Quartic.StagePullback.MetadataArithmetic

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells
open StageMain StagePullback

/-- Step 4 of `sec:algorithm`, `imp:partition` and `imp:seed`,
paper/paper.tex: actual source
scalars determine all row, column, radix and corner-selector metadata. -/
def entryPointMetadata : St VV MM := .seq rowDimensionProgram
  (.seq metadataProgram (.seq decodeEntryCoordinates
    (.seq (.op (.zero Flips.leftFlag)) (.op (.zero Flips.rightFlag)))))

/-- `prop:time`, paper/paper.tex: the metadata
producer retains every original source and sample field outside its
actual arithmetic decoder variables and corner selectors. -/
def entryMetadataScratch : List (Fin VV) :=
  [70, 71, a1, c4] ++ metadataScratch ++ [25, 26, 27, 28, 66, 67, Flips.leftFlag, Flips.rightFlag]

/-- Step 4 of `sec:algorithm`, `imp:partition`, `imp:seed` and
`prop:time`, paper/paper.tex: the complete actual numeric header physically produces the
canonical point-loop metadata, rather than assuming a decoded point. -/
theorem entryPointMetadata_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (ha : EntryHeader r a)
    (hwidth : r.call.n + 4 ≤ C.Wd) :
    Hs C entryPointMetadata a (20 * r.call.n + 100) (fun b =>
      PointData b (entryPointRequest r false false) ∧ b.sh = a.sh ∧
      Fr a b entryMetadataScratch) := by
  let q := entryPointRequest r false false
  let hs := Cells.prepare_spec _ r.selected.1 r.selected.2
  have hk : r.selected.1.k ≤ r.call.n := hs.k_lt_n.le
  have hbp : q.parameters.b = r.selected.1.b := hs.star_b
  have hsp : q.parameters.s = r.selected.1.s := hs.star_s
  have hsn : q.parameters.s ≤ r.call.n :=
    q.parameters.s_le_b.trans ((Nat.le_mul_of_pos_left _ q.parameters.r_pos).trans q.parameters.r_mul_b_le)
  unfold entryPointMetadata
  apply Hx.hs
  refine Hs.then (rowDimensionProgram_run C a hc r.call.n r.selected.1.k hk ha.arity
    ha.scalars.witnessOffset hwidth) (fun b ⟨hbd, hbradix, hbsh, hbc, hbfr⟩ n1 hn1 => ?_)
  have hb22 : b.env 22 = q.parameters.b := (hbfr _ (by decide)).trans (ha.scalars.blockSize.trans hbp.symm)
  have hb23 : b.env 23 = q.parameters.s := (hbfr _ (by decide)).trans (ha.scalars.syndrome.trans hsp.symm)
  have hb21 : b.env 21 = q.parameters.r := (hbfr _ (by decide)).trans ha.scalars.blocks
  refine Hs.then (metadataProgram_run C b q.parameters hbc hb22 hb23 hb21 hwidth)
    (fun d ⟨hdb, hdradix, hdhalf, hdsh, hdfr⟩ n2 hn2 => ?_)
  have hdc : Cst d := hbc.of_fr hdfr (by decide)
  have hdrow : d.env 71 = 2 ^ PrimT.C4Geo.dRow q.parameters := by
    rw [hdfr _ (by decide), hbradix]
    congr 1
    exact (rowDimension_eq r.call hs).symm
  have hdcol : d.env 32 = r.column.val := (hdfr _ (by decide)).trans ((hbfr _ (by decide)).trans ha.indices.column)
  have hdval : d.env 34 = r.fieldValue.val := (hdfr _ (by decide)).trans ((hbfr _ (by decide)).trans ha.indices.fieldValue)
  have hdN : d.env 35 = r.selected.1.N := (hdfr _ (by decide)).trans ((hbfr _ (by decide)).trans ha.scalars.samplerSide)
  refine Hs.then (decodeEntryCoordinates_run C r d hdc hdcol hdval hdN hdrow hwidth)
    (fun e ⟨herow, hecol, heleft, heright, hesh, hec, hefr⟩ n3 hn3 => ?_)
  refine Hs.then (hs_zero C Flips.leftFlag e) (fun f hf n4 hn4 => ?_)
  subst hf
  refine Hs.last (hs_zero C Flips.rightFlag (e.set Flips.leftFlag 0)) ?_
  rintro f hf n5 hn5
  subst hf
  let f := (e.set Flips.leftFlag 0).set Flips.rightFlag 0
  have hfzero : Fr e f [Flips.leftFlag, Flips.rightFlag] :=
    (Fr.set e _ (by simp)).trans (Fr.set _ _ (by simp))
  have hframe1 : Fr a b entryMetadataScratch := hbfr.weaken (by
    intro x hx
    simp only [entryMetadataScratch, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto)
  have hframe2 : Fr b d entryMetadataScratch := hdfr.weaken (by
    intro x hx
    simp only [entryMetadataScratch, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto)
  have hframe3 : Fr d e entryMetadataScratch := hefr.weaken (by
    intro x hx
    simp only [entryMetadataScratch, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto)
  have hframe4 : Fr e f entryMetadataScratch := hfzero.weaken (by
    intro x hx
    simp only [entryMetadataScratch, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto)
  have hf : Fr a f entryMetadataScratch := hframe1.trans (hframe2.trans (hframe3.trans hframe4))
  have hfields : ∀ i : Fin 9, f.env (pointFieldRegister i) =
      q.fields[i.val]'(by rw [PointRequest.fields_length]; exact i.isLt) := by
    intro i
    fin_cases i
    · exact (hf _ (by decide)).trans ha.arity
    · exact (hf _ (by decide)).trans ha.scalars.blocks
    · exact (hf _ (by decide)).trans (ha.scalars.blockSize.trans hbp.symm)
    · exact (hf _ (by decide)).trans (ha.scalars.syndrome.trans hsp.symm)
    · exact (hf _ (by decide)).trans ha.indices.translation
    · exact (hfzero _ (by decide)).trans herow
    · exact (hfzero _ (by decide)).trans hecol
    · exact (hfzero _ (by decide)).trans heleft
    · exact (hfzero _ (by decide)).trans heright
  have hfc : Cst f := hec.of_fr hfzero (by decide)
  have hpoint : PointData f q :=
    ⟨hfc, hfields, by simp [f, Flips.leftFlag, Flips.rightFlag, q, entryPointRequest],
      by simp [f, q, entryPointRequest],
      (hfzero _ (by decide)).trans ((hefr _ (by decide)).trans hdhalf),
      (hfzero _ (by decide)).trans ((hefr _ (by decide)).trans hdb),
      (hfzero _ (by decide)).trans ((hefr _ (by decide)).trans hdradix)⟩
  refine ⟨⟨hpoint, hesh.trans (hdsh.trans hbsh), hf⟩, ?_⟩
  change n2 ≤ 7 * q.parameters.s + 20 at hn2
  omega

end NearQuarticWires.StageMainMask
