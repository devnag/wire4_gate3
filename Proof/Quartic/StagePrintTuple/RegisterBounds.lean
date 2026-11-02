import Proof.Wire_3_5.FinalPassLiftR

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `prop:time`, paper/paper.tex: an actual
bounded-capacity word-program execution preserves that bound for every
working unary register. This permits paying local scratch cleanup by
the local monomial capacity rather than the complete Terms census. -/
theorem wordRegisters_bounded {ns nr cap : ℕ} {P : WM ns nr}
    {σ τ : WState ns nr} {steps : ℕ} (h : WExec cap P σ τ steps) :
    (∀ r,σ.val r≤cap) → ∀ r,τ.val r≤cap := by
  induction h with
  | skip => exact id
  | inc r σ hr =>
    intro hs q
    by_cases hq : q=r
    · subst q;simp only [WState.setv_val,Function.update_self];omega
    · simpa only [WState.setv_val,Function.update_of_ne hq] using hs q
  | dec r σ _hr =>
    intro hs q
    by_cases hq : q=r
    · subst q
      simp only [WState.setv_val,Function.update_self]
      exact (Nat.sub_le _ _).trans (hs r)
    · simpa only [WState.setv_val,Function.update_of_ne hq] using hs q
  | fwd => exact id
  | bwd => exact id
  | wr => exact id
  | setc => exact id
  | seq _ _ ih1 ih2 => exact fun hs=>ih2 (ih1 hs)
  | ifrT _ _ ih => exact ih
  | ifrF _ _ ih => exact ih
  | ifsT _ _ ih => exact ih
  | ifsF _ _ ih => exact ih
  | whrF => exact id
  | whrT _ _ _ ih1 ih2 => exact fun hs=>ih2 (ih1 hs)
  | whsF => exact id
  | whsT _ _ _ ih1 ih2 => exact fun hs=>ih2 (ih1 hs)
  | mono _ _ ih => exact ih

end NearQuarticWires.StageTuple
