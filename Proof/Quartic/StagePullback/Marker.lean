import Proof.Quartic.StagePullback.Digit

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.Markers

open NearCubicGates.Close.Cells

def result : Fin VV := 87
def wanted : Fin VV := 88

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: compare the extracted block digit to the one-hot marker. -/
def program : St VV MM := .seq Digits.program
  (.ite (.eq Digits.digit wanted) (.op (.copy result v1)) (.op (.zero result)))

def scratch : List (Fin VV) := Digits.scratch ++ [result]

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the one-hot marker is computed by a literal finite
division loop and a comparison, retaining its canonical inputs. -/
theorem program_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (hr : 0 < a.env Digits.radix) (hrfit : 2 * a.env Digits.radix ≤ 2 ^ C.Wd)
    (hbfit : a.env Digits.block < 2 ^ C.Wd) :
    Hs C program a (7 * a.env Digits.block + 11) (fun b =>
      b.env result = (decide (a.env Digits.number / a.env Digits.radix ^ a.env Digits.block %
        a.env Digits.radix = a.env wanted)).toNat ∧ b.sh = a.sh ∧ Fr a b scratch) := by
  unfold program
  refine Hs.seq (t1 := 7 * a.env Digits.block + 8) (t2 := 2)
    (Digits.program_run C a hr hrfit hbfit) ?_
  rintro b ⟨hdigit, hsh, hfr⟩
  have hbc : Cst b := Cst.of_fr hc hfr (by decide)
  have hw : b.env wanted = a.env wanted := hfr wanted (by decide)
  refine Hs.ite (show Digits.digit ≠ wanted by decide) (fun he => ?_) (fun he => ?_)
  · have heq : a.env Digits.number / a.env Digits.radix ^ a.env Digits.block %
        a.env Digits.radix = a.env wanted := by
      simpa only [Cnd.eval, hdigit, hw, decide_eq_true_eq] using he
    refine Hs.mono (hs_copy C result v1 b (by decide)) le_rfl ?_
    rintro e rfl
    refine ⟨by simp only [DS.set_env_self, hbc.one, heq, decide_true, Bool.toNat_true], hsh, ?_⟩
    exact (hfr.weaken (by intro x hx; exact List.mem_append_left _ hx)).trans
      (Fr.set b _ (by simp [scratch]))
  · have hne : a.env Digits.number / a.env Digits.radix ^ a.env Digits.block %
        a.env Digits.radix ≠ a.env wanted := by
      simpa only [Cnd.eval, hdigit, hw, decide_eq_false_iff_not] using he
    refine Hs.mono (hs_zero C result b) le_rfl ?_
    rintro e rfl
    refine ⟨by simp only [DS.set_env_self, hne, decide_false, Bool.toNat_false], hsh, ?_⟩
    exact (hfr.weaken (by intro x hx; exact List.mem_append_left _ hx)).trans
      (Fr.set b _ (by simp [scratch]))

end NearQuarticWires.StagePullback.Markers
