import Proof.Quartic.StagePullback.Side
import Proof.Quartic.StagePullback.SignedFlip

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.NativeRows

open NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

def transposeFlag : Fin VV := 34
def leftStore : Fin MM := 0
def rightStore : Fin MM := 1

/-- `imp:pullback` and `lem:print`, paper/paper.tex: transpose physically exchanges the two canonical side
destinations used by the certificate's column order. -/
def orientedSideProgram : St VV MM :=
  .seq Sides.program (xorInto Sides.result transposeFlag)

/-- `imp:pullback` and `lem:print`, paper/paper.tex: side placement is computed from the actual original
coordinate and then physically swapped exactly when requested. -/
theorem orientedSideProgram_run (C : Ctx) (a : DS VV MM)
    (P : StarParams) (x : Fin P.n) (transpose : Bool) (hc : Cst a)
    (hx : a.env MarkerCalls.originalCoordinate = x.val)
    (hl : a.env Sides.leftEnd = P.r / 2 * P.b) (hb : a.env Sides.blockedEnd = P.r * P.b)
    (hf : a.env Sides.freeLeftEnd = P.r * P.b + (P.n - P.r * P.b + 1) / 2)
    (ht : a.env transposeFlag = transpose.toNat) :
    Hs C orientedSideProgram a 8 (fun b =>
      b.env Sides.result = (xor (P.centerSide x) transpose).toNat ∧
      b.sh = a.sh ∧ Fr a b [Sides.result, vJ]) := by
  unfold orientedSideProgram
  refine Hs.seq (t1 := 4) (t2 := 3) (Sides.program_run C a P x hc hx hl hb hf)
    (fun b ⟨hv, hs, hfr⟩ => ?_)
  have hbc : Cst b := hc.of_fr hfr (by decide)
  have hbt : b.env transposeFlag = transpose.toNat := (hfr _ (by decide)).trans ht
  refine Hs.mono (xorInto_run C Sides.result transposeFlag (by decide) (by decide)
    (by decide) b hbc (P.centerSide x) transpose hv hbt) le_rfl ?_
  rintro d ⟨hd, hds, hdf⟩
  have hf' : Fr a b [Sides.result, vJ] := hfr.weaken (by
    intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact List.mem_cons_self ..)
  exact ⟨hd, hds.trans hs, hf'.trans hdf⟩

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the signed coefficient is physically appended to its
computed native left or right row store. -/
def routeProgram : St VV MM :=
  .ite (.eq Sides.result v1)
    (.op (.wrM leftStore SignedCoefficients.value))
    (.op (.wrM rightStore SignedCoefficients.value))

/-- `imp:pullback`, paper/paper.tex: native row routing
uses one actual binary record write at the computed side, preserving the
coefficient and its physical signed representation exactly. -/
theorem routeProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (isLeft : Bool)
    (hs : a.env Sides.result = isLeft.toNat)
    (hl : a.rc leftStore ≤ (a.ram leftStore).length)
    (hr : a.rc rightStore ≤ (a.ram rightStore).length) :
    Hs C routeProgram a 2 (fun b => b =
      (if isLeft then a.put leftStore (a.env SignedCoefficients.value)
       else a.put rightStore (a.env SignedCoefficients.value))) := by
  unfold routeProgram
  cases isLeft with
  | false =>
    exact Hs.iteF (show Sides.result ≠ v1 by decide) (by simp [Cnd.eval, hs, hc.one])
      (hs_wrM C rightStore SignedCoefficients.value a hr)
  | true =>
    exact Hs.iteT (show Sides.result ≠ v1 by decide) (by simp [Cnd.eval, hs, hc.one])
      (hs_wrM C leftStore SignedCoefficients.value a hl)

end NearQuarticWires.StagePullback.NativeRows
