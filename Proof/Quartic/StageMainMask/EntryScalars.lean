import Proof.Quartic.StageMain.ParameterGet

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicGates.Close.Cells
open StageMain StageLift

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the original parameter record supplies block count, syndrome width,
block size, sampler side, population threshold and witness offset. -/
def loadEntryScalars : St VV MM :=
  .seq (readParameter 3 21) (.seq (readParameter 4 23)
    (.seq (readParameter 5 22) (.seq (readParameter 7 35)
      (.seq (readParameter 10 36) (readParameter 6 38)))))

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
these are the exact original parameter fields retained by the entry. -/
structure EntryScalars (a : DS VV MM) (p : Cells.Parameters) : Prop where
  blocks : a.env 21 = p.r
  syndrome : a.env 23 = p.s
  blockSize : a.env 22 = p.b
  samplerSide : a.env 35 = p.N
  populationThreshold : a.env 36 = p.tau
  witnessOffset : a.env 38 = p.k

/-- `prop:time`, paper/paper.tex: the fixed scalar
reader modifies only its actual memory-access and destination registers. -/
def entryScalarScratch : List (Fin VV) := [t2, vJ, c0, 21, 23, 22, 35, 36, 38]

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: six paid original parameter-store reads give
the exact numeric metadata without any supplied decoded scalar premise. -/
theorem loadEntryScalars_run (C : Ctx) (p : Cells.Parameters) (a : DS VV MM)
    (hc : Cst a) (hstore : a.ram parameterStore = parameterScalars p)
    (hfit : 10 < 2 ^ C.Wd) :
    Hs C loadEntryScalars a (a.rc parameterStore + 400) (fun b =>
      EntryScalars b p ∧ parameterRest b = parameterRest a ∧ Cst b ∧
      Fr a b entryScalarScratch) := by
  unfold loadEntryScalars
  apply Hx.hs
  refine Hs.then (readParameter_run C p 3 21 a hc hstore (by omega) (by decide))
    (fun b ⟨hbv, hbrc, hbrest, hbc, hbfr⟩ n1 hn1 => ?_)
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.2.1) hbrest
  refine Hs.then (readParameter_run C p 4 23 b hbc (hbram ▸ hstore) (by omega) (by decide))
    (fun c ⟨hcv, hcrc, hcrest, hcc, hcfr⟩ n2 hn2 => ?_)
  have hcram : c.ram = b.ram := congrArg (fun t => t.2.2.1) hcrest
  refine Hs.then (readParameter_run C p 5 22 c hcc (hcram ▸ hbram ▸ hstore) (by omega) (by decide))
    (fun d ⟨hdv, hdrc, hdrest, hdc, hdfr⟩ n3 hn3 => ?_)
  have hdram : d.ram = c.ram := congrArg (fun t => t.2.2.1) hdrest
  refine Hs.then (readParameter_run C p 7 35 d hdc (hdram ▸ hcram ▸ hbram ▸ hstore) (by omega) (by decide))
    (fun e ⟨hev, herc, herest, hec, hefr⟩ n4 hn4 => ?_)
  have heram : e.ram = d.ram := congrArg (fun t => t.2.2.1) herest
  refine Hs.then (readParameter_run C p 10 36 e hec
    (heram ▸ hdram ▸ hcram ▸ hbram ▸ hstore) hfit (by decide))
    (fun f ⟨hfv, hfrc, hfrest, hfc, hffr⟩ n5 hn5 => ?_)
  have hfram : f.ram = e.ram := congrArg (fun t => t.2.2.1) hfrest
  refine Hs.last (readParameter_run C p 6 38 f hfc
    (hfram ▸ heram ▸ hdram ▸ hcram ▸ hbram ▸ hstore) (by omega) (by decide)) ?_
  rintro g ⟨hgv, _hgrc, hgrest, hgc, hgfr⟩ n6 hn6
  have hb : g.env 21 = p.r := by
    rw [hgfr _ (by decide), hffr _ (by decide), hefr _ (by decide), hdfr _ (by decide), hcfr _ (by decide), hbv]
    rfl
  have hs : g.env 23 = p.s := by
    rw [hgfr _ (by decide), hffr _ (by decide), hefr _ (by decide), hdfr _ (by decide), hcv]
    rfl
  have hbs : g.env 22 = p.b := by
    rw [hgfr _ (by decide), hffr _ (by decide), hefr _ (by decide), hdv]
    rfl
  have hN : g.env 35 = p.N := by
    rw [hgfr _ (by decide), hffr _ (by decide), hev]
    rfl
  have ht : g.env 36 = p.tau := by rw [hgfr _ (by decide), hfv]; rfl
  have hk : g.env 38 = p.k := hgv
  have hf1 : Fr a b entryScalarScratch := hbfr.weaken (by
    intro x hx
    simp only [entryScalarScratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto)
  have hf2 : Fr b c entryScalarScratch := hcfr.weaken (by
    intro x hx
    simp only [entryScalarScratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto)
  have hf3 : Fr c d entryScalarScratch := hdfr.weaken (by
    intro x hx
    simp only [entryScalarScratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto)
  have hf4 : Fr d e entryScalarScratch := hefr.weaken (by
    intro x hx
    simp only [entryScalarScratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto)
  have hf5 : Fr e f entryScalarScratch := hffr.weaken (by
    intro x hx
    simp only [entryScalarScratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto)
  have hf6 : Fr f g entryScalarScratch := hgfr.weaken (by
    intro x hx
    simp only [entryScalarScratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto)
  have hframe : Fr a g entryScalarScratch := hf1.trans (hf2.trans (hf3.trans (hf4.trans (hf5.trans hf6))))
  refine ⟨⟨⟨hb, hs, hbs, hN, ht, hk⟩,
    hgrest.trans (hfrest.trans (herest.trans (hdrest.trans (hcrest.trans hbrest)))), hgc, hframe⟩, ?_⟩
  rw [hbrc] at hn2
  rw [hcrc] at hn3
  rw [hdrc] at hn4
  rw [herc] at hn5
  rw [hfrc] at hn6
  norm_num at hn1 hn2 hn3 hn4 hn5 hn6
  omega

end NearQuarticWires.StageMainMask
