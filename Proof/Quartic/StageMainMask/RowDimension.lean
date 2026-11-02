import Proof.Quartic.StageMainMask.EntryArity
import Proof.Gates.Cells.Arith

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `imp:partition`, paper/paper.tex: the canonical
left center dimension is the ceiling half of the original free center
bits, by the exact balanced shared-generator partition. -/
theorem rowDimension_eq (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) :
    PrimT.C4Geo.dRow (Builder.star c hs) = (c.n - p.k + 1) / 2 := by
  have hsum := (Builder.star c hs).centerBits_sum
  rw [hs.star_k] at hsum
  have hbal := (Builder.star c hs).centerBits_balanced
  change (Builder.star c hs).leftCenterBits = _
  change (Builder.star c hs).leftCenterBits + (Builder.star c hs).rightCenterBits = c.n - p.k at hsum
  omega

/-- `imp:partition` and Step 4 of `sec:algorithm`, paper/paper.tex: the original n and selected k are used to
compute the exact row dimension and its binary quotient radix. -/
def rowDimensionProgram : St VV MM :=
  .seq (.op (.copy 70 20)) (.seq (.op (.sub 70 38))
    (.seq (.op (.inc 70)) (.seq (.op (.half 70)) (powP v2 70 71))))

/-- `imp:partition` and `prop:time`, paper/paper.tex: the actual row-dimension radix is physically computed
from source n and k, with all scalar and exponentiation work charged. -/
theorem rowDimensionProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (n k : ℕ) (hk : k ≤ n) (hn : a.env 20 = n) (hkey : a.env 38 = k)
    (hwidth : n + 4 ≤ C.Wd) :
    Hs C rowDimensionProgram a (7 * n + 30) (fun b =>
      b.env 70 = (n - k + 1) / 2 ∧ b.env 71 = 2 ^ ((n - k + 1) / 2) ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b [70, 71, a1, c4]) := by
  have hcap : n + 1 < 2 ^ C.Wd :=
    (Nat.lt_two_pow_self (n := n + 1)).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  unfold rowDimensionProgram
  apply Hx.hs
  refine Hs.then (hs_copy C 70 20 a (by decide)) (fun b he n1 hn1 => ?_)
  subst he
  let b := a.set 70 (a.env 20)
  have hb : b.env 70 = n := by simp [b, hn]
  have hbk : b.env 38 = k := (DS.set_env_ne _ _ (by decide)).trans hkey
  refine Hs.then (hs_sub C 70 38 b (by decide) (by rw [hb, hbk]; exact hk))
    (fun d he n2 hn2 => ?_)
  subst he
  let d := b.set 70 (b.env 70 - b.env 38)
  have hd : d.env 70 = n - k := by simp [d, hb, hbk]
  refine Hs.then (hs_inc C 70 d (by rw [hd]; omega)) (fun e he n3 hn3 => ?_)
  subst he
  let e := d.set 70 (d.env 70 + 1)
  have he : e.env 70 = n - k + 1 := by simp [e, hd]
  refine Hs.then (hs_half C 70 e) (fun f hf n4 hn4 => ?_)
  subst hf
  let f := e.set 70 (e.env 70 / 2)
  have hf : f.env 70 = (n - k + 1) / 2 := by simp [f, he]
  have hfr : Fr a f [70] := (Fr.set a _ (by simp)).trans
    ((Fr.set b _ (by simp)).trans ((Fr.set d _ (by simp)).trans (Fr.set e _ (by simp))))
  have hfc : Cst f := hc.of_fr hfr (by decide)
  have hpow := powP_spec (C := C) v2 70 71 (by decide) f (by
    intro j hj
    rw [hf] at hj
    rw [hfc.two]
    exact Nat.pow_lt_pow_right (by decide) (by omega))
    (by rw [hf]; have := Nat.div_le_self (n - k + 1) 2; omega)
    (Nat.one_lt_two_pow (by omega))
  refine Hs.last hpow ?_
  rintro g ⟨hgv, hgsh, hgfr⟩ n5 hn5
  have hfull : Fr a g [70, 71, a1, c4] :=
    (hfr.weaken (by simp)).trans (hgfr.weaken (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      tauto))
  refine ⟨⟨(hgfr _ (by decide)).trans hf, by simpa only [hfc.two, hf] using hgv,
    hgsh, hfc.of_fr hgfr (by decide), hfull⟩, ?_⟩
  rw [hf] at hn5
  have := Nat.div_le_self (n - k + 1) 2
  omega

end NearQuarticWires.StageMainMask
