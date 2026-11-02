import Proof.Gates.Dispatch.ParamsG

/-!
# Exact arithmetic public guards

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- A computed public inequality in `sec:params`,
paper/paper.tex, clears the admission flag
exactly when its integer comparison fails. -/
def checkedLe (dst rhs : Fin VV) (e : AE) : St VV :=
  .seq (assign dst e) (needLe dst rhs)

/-- The arithmetic guard of `sec:params`, paper/paper.tex, has its exact conjunction semantics and pays
for the complete expression evaluation on either outcome. -/
theorem checkedLe_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (dst rhs : Fin VV) (e : AE) (P : Prop) [Decidable P]
    (hP : a.env vADM = bnat P) (hdst : dst.val < 200)
    (hsafe : dst ∉ [vZ, v1, v2, vPOS]) (hda : vADM ≠ dst)
    (hrd : rhs ≠ dst) (hrj : rhs ≠ vJ) (hrsmall : rhs.val < 200)
    (hevars : e.vars_ok) (hedepth : e.depth + 1 < 50) (heok : e.ok C.Wd a.env) :
    Hs C (checkedLe dst rhs e) a (e.cost + 5) (fun b =>
      b.env vADM = bnat (P ∧ e.eval a.env ≤ a.env rhs) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [dst, vADM, vJ]) := by
  unfold checkedLe
  refine Hx.hs (Hs.then (assign_spec dst hdst hsafe e a hevars hedepth hc heok)
    (fun b ⟨hbe, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hbP : b.env vADM = bnat P := (hbfr _ (by decide) (by decide) hda).trans hP
  have hbr : b.env rhs = a.env rhs := hbfr rhs hrsmall hrj hrd
  refine Hs.last (needLe_spec dst rhs hrd b P hbP) ?_
  rintro d ⟨hdf, hdcp, hdwq, hdout, hdfr⟩ n2 hn2
  have F : FrS a d [dst, vADM, vJ] :=
    FrS.trans (hbfr.toS _ (by simp) (by simp)) (FrS.weaken hdfr.toS (by simp))
  refine ⟨⟨?_, hdcp.trans hbcp, hdwq.trans hbwq, hdout.trans hbout,
    Cst.of_fr hbc hdfr (by decide)
      (by rw [hdfr vPOS (by decide), hdcp]; exact hbc.pos), F⟩, by omega⟩
  rw [hdf, hbe, hbr]

end NearQuarticWires.StagePrep
