import Proof.Quartic.StageCert.StructuralReply

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `sec:walks` and `lem:print`, paper/paper.tex: fixed scratch for an actual low-first radix-N walk digit. -/
def patternBase : Fin VV := ⟨85,by decide⟩
def patternRemaining : Fin VV := ⟨86,by decide⟩
def patternQuotient : Fin VV := ⟨87,by decide⟩
def patternRemainder : Fin VV := ⟨88,by decide⟩

/-- `sec:walks`, paper/paper.tex: remove one
actual base-N digit by binary quotient and remainder arithmetic. -/
def dividePatternOnce : St VV MM :=
  .seq (.op (.dm patternRemaining patternBase patternQuotient patternRemainder))
    (.op (.copy patternRemaining patternQuotient))

/-- `sec:walks` and `prop:time`, paper/paper.tex: actual division changes only three numeric scratch
registers and leaves the complete original source untouched. -/
theorem dividePatternOnce_run (C : Ctx) (N value : ℕ) (a : DS VV MM)
    (hc : Cst a) (hN : 0<N) (hb : a.env patternBase=N)
    (hv : a.env patternRemaining=value) (hfit : 2*N≤2^C.Wd) :
    Hs C dividePatternOnce a 3 (fun z=>
      z.env patternRemaining=value/N ∧ z.sh=a.sh ∧ Cst z ∧
      Fr a z [patternRemaining,patternQuotient,patternRemainder]) := by
  unfold dividePatternOnce
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_dm C patternRemaining patternBase patternQuotient patternRemainder a
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hb]; exact hN) (by rw [hb]; exact hfit)) ?_
  rintro b rfl
  refine (hs_copy C patternRemaining patternQuotient _ (by decide)).mono le_rfl ?_
  rintro z rfl
  have hf : Fr a (((a.set patternQuotient (a.env patternRemaining/a.env patternBase)).set
      patternRemainder (a.env patternRemaining%a.env patternBase)).set patternRemaining
      (a.env patternRemaining/a.env patternBase))
      [patternRemaining,patternQuotient,patternRemainder] :=
    (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))
  refine ⟨?_,rfl,Cst.of_fr hc hf (by decide),hf⟩
  change a.env patternRemaining/a.env patternBase=value/N
  rw [hv,hb]

/-- `sec:walks`, paper/paper.tex: a static slot
uses at most seven actual divisions, with no padded field enumeration. -/
def dividePattern : ℕ→St VV MM
  | 0 => .op (.zero patternRemainder)
  | slot+1 => .seq (dividePattern slot) dividePatternOnce

/-- `sec:walks` and `prop:time`, paper/paper.tex: the remaining numeric word is the exact original
ordinal divided by N to the requested slot power. -/
theorem dividePattern_run (C : Ctx) (N index slot : ℕ) (a : DS VV MM)
    (hc : Cst a) (hN : 0<N) (hb : a.env patternBase=N)
    (hv : a.env patternRemaining=index) (hfit : 2*N≤2^C.Wd) :
    Hs C (dividePattern slot) a (4*slot+1) (fun z=>
      z.env patternRemaining=index/N^slot ∧ z.sh=a.sh ∧ Cst z ∧
      Fr a z [patternRemaining,patternQuotient,patternRemainder]) := by
  induction slot with
  | zero =>
    refine (hs_zero C patternRemainder a).mono le_rfl ?_
    rintro z rfl
    exact ⟨by change a.env patternRemaining=index/1; simpa using hv,
      rfl,Cst.of_fr hc (Fr.set _ _ (T := [patternRemainder]) (by simp)) (by decide),
      Fr.set _ _ (by simp)⟩
  | succ slot ih =>
    unfold dividePattern
    apply Hx.hs
    refine Hs.then ih (fun b ⟨bv,bs,bc,bf⟩ n1 hn1=>?_)
    refine Hs.last (dividePatternOnce_run C N (index/N^slot) b bc hN
      ((bf _ (by decide)).trans hb) bv hfit)
      (fun z ⟨zv,zs,zc,zf⟩ n2 hn2=>?_)
    refine ⟨⟨?_,zs.trans bs,zc,bf.trans zf⟩,by omega⟩
    rw [zv,Nat.div_div_eq_div_mul,pow_succ]

end NearQuarticWires.StageCert.Tokens
