import Proof.Quartic.StageCertificateControl.CountStart

/-!
# A common register capacity for certificate stages

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

variable {ns nr small large n : ℕ} {σ τ : WState ns nr}

/-- `prop:time`, paper/paper.tex: increasing
the register capacity preserves the same physical instructions and clock. -/
theorem register_capacity {P : WM ns nr} (h : WExec small P σ τ n) (hc : small≤large) :
    WExec large P σ τ n := by
  induction h with
  | skip a => exact .skip a
  | inc r a h => exact .inc r a (lt_of_lt_of_le h hc)
  | dec r a h => exact .dec r a (h.trans hc)
  | fwd i a => exact .fwd i a
  | bwd i a => exact .bwd i a
  | wr i b a => exact .wr i b a
  | setc b a => exact .setc b a
  | seq _ _ i1 i2 => exact .seq i1 i2
  | ifrT h _ ih => exact .ifrT h ih
  | ifrF h _ ih => exact .ifrF h ih
  | ifsT h _ ih => exact .ifsT h ih
  | ifsF h _ ih => exact .ifsF h ih
  | whrF h => exact .whrF h
  | whrT h _ _ i1 i2 => exact .whrT h i1 i2
  | whsF h => exact .whsF h
  | whsT h _ _ i1 i2 => exact .whsT h i1 i2
  | mono _ hm ih => exact .mono ih hm

/-- `prop:time`, paper/paper.tex: a common
capacity composes real subroutines without changing their executions. -/
theorem word_capacity {P : WMX ns nr} (h : WXExec small P σ τ n) (hc : small≤large) :
    WXExec large P σ τ n := by
  induction h with
  | wm h => exact .wm (register_capacity h hc)
  | mach a hi he => exact .mach a hi he
  | seq _ _ i1 i2 => exact .seq i1 i2
  | ifrT h _ ih => exact .ifrT h ih
  | ifrF h _ ih => exact .ifrF h ih
  | ifsT h _ ih => exact .ifsT h ih
  | ifsF h _ ih => exact .ifsF h ih
  | whrF h => exact .whrF h
  | whrT h _ _ i1 i2 => exact .whrT h i1 i2
  | whsF h => exact .whsF h
  | whsT h _ _ i1 i2 => exact .whsT h i1 i2
  | mono _ hm ih => exact .mono ih hm

end NearQuarticWires.StageCertificateControl
