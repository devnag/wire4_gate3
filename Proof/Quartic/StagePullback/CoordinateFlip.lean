import Proof.Quartic.StagePullback.Flip

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.Flips

open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

/-- `imp:pullback`, paper/paper.tex: a physical
corner bit controls whether its decoded error is xored into the retained
translation marker. -/
def selectedError (right : Bool) : St VV MM :=
  .ite (.eq (flagRegister right) v1)
    (.seq (errorCall right) (xorInto accumulator Markers.result)) skipS

/-- `imp:pullback` and `prop:time`, paper/paper.tex: one selected star error is computed from its actual
pattern code and physically combined with the incoming bit. -/
theorem selectedError_run (C : Ctx) (a : DS VV MM) (q : PointRequest)
    (x : Fin q.parameters.n) (hi : Inputs a q x) (right : Bool)
    (hwidth : q.parameters.n + 4 ≤ C.Wd) (u : Bool)
    (hu : a.env accumulator = u.toNat) :
    Hs C (selectedError right) a (7 * (x.val / q.parameters.b) + 38) (fun b =>
      b.env accumulator = (xor u
        (errorFlag q right && errorBit q.parameters.b (q.parameters.r / 2)
          q.parameters.s right (errorCode q right) x.val)).toNat ∧
      b.sh = a.sh ∧ Fr a b scratch) := by
  have hflag : a.env (flagRegister right) = (errorFlag q right).toNat := by
    cases right <;> first | exact hi.useLeft | exact hi.useRight
  have hwf : flagRegister right ≠ v1 := by cases right <;> decide
  unfold selectedError
  refine Hs.ite (t := 7 * (x.val / q.parameters.b) + 37) hwf (fun h => ?_) (fun h => ?_)
  · have hchosen : errorFlag q right = true := by
      cases he : errorFlag q right <;> simp [Cnd.eval, hflag, hi.constants.one, he] at h ⊢
    refine Hx.hs (Hs.then (errorCall_run C a q x hi right hwidth)
      (fun b ⟨hv, hsh, hfr⟩ n1 hn1 => ?_))
    have hf : Fr a b scratch :=
      hfr.weaken (by intro y hy; exact List.mem_cons_of_mem accumulator hy)
    have hb := hi.frame hf
    have hacc : b.env accumulator = u.toNat := (hfr _ (by decide)).trans hu
    refine Hs.last (xorInto_run C accumulator Markers.result (by decide) (by decide)
      (by decide) b hb.constants u
      (errorBit q.parameters.b (q.parameters.r / 2) q.parameters.s right (errorCode q right) x.val)
      hacc hv) ?_
    rintro d ⟨hd, hds, hdf⟩ n2 hn2
    have hdf' : Fr b d scratch := hdf.weaken (by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> decide)
    exact ⟨⟨by simpa only [hchosen, Bool.true_and] using hd, hds.trans hsh,
      hf.trans hdf'⟩, by omega⟩
  · have hchosen : errorFlag q right = false := by
      cases he : errorFlag q right <;> simp [Cnd.eval, hflag, hi.constants.one, he] at h ⊢
    refine Hs.mono (skip_spec a) (by omega) ?_
    rintro b rfl
    exact ⟨by simpa [hchosen] using (show (a.set vJ 0).env accumulator = u.toNat from
      (DS.set_env_ne _ _ (by decide : accumulator ≠ vJ)).trans hu), rfl,
      Fr.set a _ (by decide)⟩

/-- `imp:pullback`, paper/paper.tex: the translation
marker is computed from the full block count and its retained scalar code. -/
def translationCall : St VV MM := MarkerCalls.leftCall 21 24

/-- `imp:pullback` and `prop:time`, paper/paper.tex: actual translation decoding precedes the two selected
error computations, with the original coordinate retained throughout. -/
theorem translationCall_run (C : Ctx) (a : DS VV MM) (q : PointRequest)
    (x : Fin q.parameters.n) (hi : Inputs a q x)
    (hwidth : q.parameters.n + 4 ≤ C.Wd) :
    Hs C translationCall a (7 * (x.val / q.parameters.b) + 32) (fun b =>
      b.env Markers.result = (offsetBit q.parameters.r q.parameters.b q.parameters.s
        (translationNumber q.parameters q.translation) x.val).toNat ∧
      b.sh = a.sh ∧ Fr a b MarkerCalls.scratch) := by
  have hw := markerWidth C q.parameters hwidth
  have hrun := MarkerCalls.leftCall_run C a hi.constants 21 24 (by decide) (by decide)
    (by rw [hi.blockWidth]; exact q.parameters.b_pos)
    (by rw [hi.blockWidth]; exact hw.1)
    (by rw [hi.blockWidth, hi.blocks]; exact hw.2.1)
    (by rw [hi.coordinate]; exact x.isLt.trans hw.2.2.2)
    (by rw [hi.radix]; exact Nat.two_pow_pos _)
    (by rw [hi.radix]; exact hw.2.2.1)
  refine Hs.mono hrun (by rw [hi.coordinate, hi.blockWidth]) ?_
  rintro b ⟨hv, hs, hf⟩
  exact ⟨by simpa [hi.coordinate, hi.blockWidth, hi.blocks, hi.translation,
    hi.radix, offsetBit, blockDigit] using hv, hs, hf⟩

/-- `imp:pullback`, paper/paper.tex: the literal
canonical affine flip computes its translation and both selected errors
from their compact scalar codes. -/
def program : St VV MM :=
  .seq translationCall (.seq (.op (.copy accumulator Markers.result))
    (.seq (selectedError false) (selectedError true)))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the physical coordinate program returns exactly the
actual canonical translation xor the two selected star errors. -/
theorem program_run (C : Ctx) (a : DS VV MM) (q : PointRequest)
    (x : Fin q.parameters.n) (hi : Inputs a q x)
    (hwidth : q.parameters.n + 4 ≤ C.Wd) :
    Hs C program a (21 * (x.val / q.parameters.b) + 120) (fun b =>
      b.env accumulator = (q.flip x).toNat ∧ b.sh = a.sh ∧ Fr a b scratch) := by
  unfold program
  refine Hx.hs (Hs.then (translationCall_run C a q x hi hwidth)
    (fun b ⟨hb, hbs, hbf⟩ n1 hn1 => ?_))
  have hf : Fr a b scratch :=
    hbf.weaken (by intro y hy; exact List.mem_cons_of_mem accumulator hy)
  have hib := hi.frame hf
  refine Hs.then (hs_copy C accumulator Markers.result b (by decide))
    (fun c hc n2 hn2 => ?_)
  subst hc
  let c := b.set accumulator (b.env Markers.result)
  have hfc : Fr b c scratch := Fr.set b _ (by simp [scratch])
  have hic : Inputs c q x := hib.frame hfc
  have hacc : c.env accumulator = (offsetBit q.parameters.r q.parameters.b q.parameters.s
      (translationNumber q.parameters q.translation) x.val).toNat := by
    rw [DS.set_env_self, hb]
  refine Hs.then (selectedError_run C c q x hic false hwidth _ hacc)
    (fun d ⟨hd, hds, hdf⟩ n3 hn3 => ?_)
  have hid := hic.frame hdf
  refine Hs.last (selectedError_run C d q x hid true hwidth _ hd) ?_
  rintro e ⟨he, hes, hef⟩ n4 hn4
  refine ⟨⟨?_, hes.trans (hds.trans hbs), hf.trans (hfc.trans (hdf.trans hef))⟩, by omega⟩
  simpa only [PointRequest.flip, flipBit, errorFlag, errorCode, Bool.false_eq_true,
    if_false, if_true] using he

end NearQuarticWires.StagePullback.Flips
