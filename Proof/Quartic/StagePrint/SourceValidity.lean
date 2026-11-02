import Proof.Gates.Cells.OutLen
import Proof.Gates.Cells.Kit

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: every actual source subroutine retains validity, so later rewind clocks are bounded by the physically retained record lengths. -/
theorem source_addValid {C : Ctx} {s : St VV MM} {a : DS VV MM} {t : ℕ} {R : DS VV MM→Prop}
    (hW : 1≤C.Wd) (ha : Valid C a) (hs : Hs C s a t R) :
    Hs C s a t (fun b=>R b ∧ Valid C b) := by
  obtain ⟨b,n,he,hn,hr⟩:=hs
  refine ⟨b,n,he,hn,hr,he.valid hW ?_ ha⟩
  intro r hb
  exact (wf_out_len C.K.wf r).trans (by omega)

end NearQuarticWires.StagePrint
