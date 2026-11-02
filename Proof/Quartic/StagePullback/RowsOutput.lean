import Proof.Quartic.StagePullback.StoreOutput

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.NativeRows

open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells

def savedTarget : Fin VV := 62

/-- `lem:print`, paper/paper.tex: retain the exact
adjusted target, serialize the two real native halves with common-width
padding, and append the original convention's adjusted signed target. -/
def rowsOutputProgram : St VV MM :=
  .seq (.op (.copy savedTarget SignedCoefficients.value))
    (.seq (storeProgram true) (.seq (storeProgram false)
      (.seq (.op (.copy SignedCoefficients.value savedTarget)) FieldOutput.program)))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual native signed halves and adjusted target are
physically emitted as their exact field-record stream with all padding. -/
theorem rowsOutputProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (xs ys : List ℕ) (W L : ℕ)
    (hramL : a.ram leftStore = xs) (hramR : a.ram rightStore = ys)
    (hrcL : a.rc leftStore = xs.length) (hrcR : a.rc rightStore = ys.length)
    (hcountL : a.env leftCount = xs.length) (hcountR : a.env rightCount = ys.length)
    (hwidth : a.env nativeWidth = W) (hfield : a.env FieldOutput.width = L)
    (hlenL : xs.length ≤ W) (hlenR : ys.length ≤ W)
    (hW : W < 2 ^ C.Wd) (hL : L < 2 ^ C.Wd) (hWd : 2 ≤ C.Wd) :
    Hs C rowsOutputProgram a (2 * W * (12 * L + 20) + 12 * L + 50) (fun b =>
      b.out = a.out ++ (padNumbers W xs ++ padNumbers W ys ++ [a.env SignedCoefficients.value]).flatMap
        (fun v => frame (binary L v))) := by
  unfold rowsOutputProgram
  refine Hx.hs (Hs.then (hs_copy C savedTarget SignedCoefficients.value a (by decide))
    (fun b hb n1 hn1 => ?_))
  subst hb
  let b := a.set savedTarget (a.env SignedCoefficients.value)
  have hbf : Fr a b [savedTarget] := Fr.set a _ (by simp)
  have hbc : Cst b := hc.of_fr hbf (by decide)
  have hbw : b.env nativeWidth = W := (hbf _ (by decide)).trans hwidth
  have hbl : b.env FieldOutput.width = L := (hbf _ (by decide)).trans hfield
  have hbcntL : b.env (selectedCount true) = xs.length := (hbf _ (by decide)).trans hcountL
  refine Hs.then (storeProgram_run C b hbc true xs W L hramL hrcL hbcntL hbw hbl hlenL hW hL hWd)
    (fun c ⟨hcout, hcip, hcram, hcrc, hcc, hcfr⟩ n2 hn2 => ?_)
  have hcw : c.env nativeWidth = W := (hcfr _ (by decide)).trans hbw
  have hcl : c.env FieldOutput.width = L := (hcfr _ (by decide)).trans hbl
  have hccntR : c.env (selectedCount false) = ys.length :=
    (hcfr _ (by decide)).trans ((hbf _ (by decide)).trans hcountR)
  have hcR : c.ram (selectedStore false) = ys := by rw [hcram]; exact hramR
  have hcrcR : c.rc (selectedStore false) = ys.length := by rw [hcrc]; exact hrcR
  refine Hs.then (storeProgram_run C c hcc false ys W L hcR hcrcR hccntR hcw hcl hlenR hW hL hWd)
    (fun d ⟨hdout, _, _, _, hdc, hdfr⟩ n3 hn3 => ?_)
  have htarget : d.env savedTarget = a.env SignedCoefficients.value :=
    (hdfr _ (by decide)).trans ((hcfr _ (by decide)).trans (DS.set_env_self _ _ _))
  have hdl : d.env FieldOutput.width = L := (hdfr _ (by decide)).trans hcl
  refine Hs.then (hs_copy C SignedCoefficients.value savedTarget d (by decide))
    (fun e he n4 hn4 => ?_)
  subst he
  let e := d.set SignedCoefficients.value (d.env savedTarget)
  have hef : Fr d e [SignedCoefficients.value] := Fr.set d _ (by simp)
  have hec : Cst e := hdc.of_fr hef (by decide)
  have hel : e.env FieldOutput.width = L := (hef _ (by decide)).trans hdl
  have hev : e.env SignedCoefficients.value = a.env SignedCoefficients.value :=
    (DS.set_env_self _ _ _).trans htarget
  refine Hs.last (FieldOutput.program_run C e hec L (a.env SignedCoefficients.value) hel hev hL hWd) ?_
  rintro f ⟨hfout, _, _, _⟩ n5 hn5
  refine ⟨?_, by nlinarith only [hn1, hn2, hn3, hn4, hn5, hlenL, hlenR]⟩
  rw [hfout]
  simp only [e, DS.set_out]
  rw [hdout, hcout]
  simp only [b, DS.set_out, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

end NearQuarticWires.StagePullback.NativeRows
