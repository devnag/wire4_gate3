import Proof.Quartic.StagePullback.Offset

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.RightErrors

open NearCubicGates.Close.Cells
open Offsets

def boundary : Fin VV := 93

/-- `imp:pullback`, paper/paper.tex: right-side block
errors use the same digit computation with the original origin shifted
past the left blocks, and vanish before that boundary. -/
def program : St VV MM := .seq (.op (.mul blockCount blockWidth boundary))
  (.ite (.lt coordinate boundary) (.op (.zero Markers.result))
    (.seq (.op (.sub coordinate boundary)) Offsets.program))

def scratch : List (Fin VV) := [boundary, coordinate] ++ Offsets.scratch

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the physical right-error computation is zero on the
left half and agrees with the actual shifted block marker thereafter. -/
theorem program_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (hb : 0 < a.env blockWidth) (hbfit : 2 * a.env blockWidth ≤ 2 ^ C.Wd)
    (hprod : a.env blockCount * a.env blockWidth < 2 ^ C.Wd)
    (hxfit : a.env coordinate < 2 ^ C.Wd)
    (hr : 0 < a.env Digits.radix) (hrfit : 2 * a.env Digits.radix ≤ 2 ^ C.Wd) :
    Hs C program a (7 * (a.env coordinate / a.env blockWidth) + 26) (fun b =>
      b.env Markers.result = (decide
        (a.env blockCount * a.env blockWidth ≤ a.env coordinate ∧
          a.env coordinate - a.env blockCount * a.env blockWidth <
            a.env blockCount * a.env blockWidth ∧
          a.env Digits.number / a.env Digits.radix ^
            ((a.env coordinate - a.env blockCount * a.env blockWidth) / a.env blockWidth) %
              a.env Digits.radix =
            (a.env coordinate - a.env blockCount * a.env blockWidth) % a.env blockWidth + 1)).toNat ∧
      b.sh = a.sh ∧ Fr a b scratch) := by
  unfold program
  refine Hx.hs (Hs.then (hs_mul C blockCount blockWidth boundary a
    (by decide) (by decide) (by decide) hprod) (fun b he n1 hn1 => ?_))
  subst he
  let a1 := a.set boundary (a.env blockCount * a.env blockWidth)
  have hc1 : Cst a1 := hc.of_fr (Fr.set a _ (show boundary ∈ [boundary] by simp)) (by decide)
  have hif : Hs C
      (.ite (.lt coordinate boundary) (.op (.zero Markers.result))
        (.seq (.op (.sub coordinate boundary)) Offsets.program)) a1
      (7 * (a.env coordinate / a.env blockWidth) + 24)
      (fun b => b.env Markers.result = (decide
        (a.env blockCount * a.env blockWidth ≤ a.env coordinate ∧
          a.env coordinate - a.env blockCount * a.env blockWidth <
            a.env blockCount * a.env blockWidth ∧
          a.env Digits.number / a.env Digits.radix ^
            ((a.env coordinate - a.env blockCount * a.env blockWidth) / a.env blockWidth) %
              a.env Digits.radix =
            (a.env coordinate - a.env blockCount * a.env blockWidth) % a.env blockWidth + 1)).toNat ∧
        b.sh = a1.sh ∧ Fr a1 b (coordinate :: Offsets.scratch)) := by
    refine Hs.ite (show coordinate ≠ boundary by decide) (fun h => ?_) (fun h => ?_)
    · have hxlt : a.env coordinate < a.env blockCount * a.env blockWidth := by
        simpa only [Cnd.eval, a1, DS.set_env_self,
          DS.set_env_ne _ _ (by decide : coordinate ≠ boundary), decide_eq_true_eq] using h
      refine Hs.mono (hs_zero C Markers.result a1) (by omega) ?_
      rintro d rfl
      refine ⟨by simp only [DS.set_env_self, show ¬ a.env blockCount * a.env blockWidth ≤
          a.env coordinate by omega, false_and, decide_false, Bool.toNat_false], rfl, ?_⟩
      exact Fr.set _ _ (by simp [Offsets.scratch, Markers.scratch])
    · have hxge : a.env blockCount * a.env blockWidth ≤ a.env coordinate := by
        have hnot : ¬ a.env coordinate < a.env blockCount * a.env blockWidth := by
          simpa only [Cnd.eval, a1, DS.set_env_self,
            DS.set_env_ne _ _ (by decide : coordinate ≠ boundary), decide_eq_false_iff_not] using h
        omega
      refine Hx.hs (Hs.then (hs_sub C coordinate boundary a1 (by decide)
        (by simpa only [a1, DS.set_env_self,
          DS.set_env_ne _ _ (by decide : coordinate ≠ boundary)] using hxge))
        (fun d hd n2 hn2 => ?_))
      subst hd
      let a2 := a1.set coordinate (a.env coordinate - a.env blockCount * a.env blockWidth)
      have henv (y : Fin VV) (hy1 : y ≠ coordinate) (hy2 : y ≠ boundary) :
          a2.env y = a.env y := by
        rw [DS.set_env_ne _ _ hy1, DS.set_env_ne _ _ hy2]
      have hcoord : a2.env coordinate = a.env coordinate - a.env blockCount * a.env blockWidth :=
        DS.set_env_self _ _ _
      have hc2 : Cst a2 := hc1.of_fr (Fr.set a1 _ (show coordinate ∈ [coordinate] by simp)) (by decide)
      have heq : (a1.set coordinate (a1.env coordinate - a1.env boundary)) = a2 := by
        simp only [a1, a2, DS.set_env_self,
          DS.set_env_ne _ _ (by decide : coordinate ≠ boundary)]
      rw [heq]
      refine Hs.last (Offsets.program_run C a2 hc2
        (by rw [henv blockWidth (by decide) (by decide)]; exact hb)
        (by rw [henv blockWidth (by decide) (by decide)]; exact hbfit)
        (by rw [henv blockCount (by decide) (by decide), henv blockWidth (by decide) (by decide)]; exact hprod)
        (by rw [hcoord]; exact (Nat.sub_le _ _).trans_lt hxfit)
        (by rw [henv Digits.radix (by decide) (by decide)]; exact hr)
        (by rw [henv Digits.radix (by decide) (by decide)]; exact hrfit)) ?_
      rintro e ⟨hev, hes, hef⟩ n3 hn3
      refine ⟨⟨?_, hes, ?_⟩, ?_⟩
      · simpa only [hcoord, henv blockWidth (by decide) (by decide),
          henv blockCount (by decide) (by decide), henv Digits.number (by decide) (by decide),
          henv Digits.radix (by decide) (by decide), hxge, true_and] using hev
      · exact (Fr.set a1 _ (List.mem_cons_self ..)).trans
          (hef.weaken (by intro y hy; exact List.mem_cons_of_mem coordinate hy))
      · rw [hcoord, henv blockWidth (by decide) (by decide)] at hn3
        have hq : (a.env coordinate - a.env blockCount * a.env blockWidth) /
            a.env blockWidth ≤ a.env coordinate / a.env blockWidth :=
          Nat.div_le_div_right (Nat.sub_le (a.env coordinate) (a.env blockCount * a.env blockWidth))
        omega
  refine Hs.last hif ?_
  rintro b ⟨hv, hs, hf⟩ n2 hn2
  refine ⟨⟨hv, hs, ?_⟩, by omega⟩
  exact (Fr.set a _ (by simp [scratch])).trans
    (hf.weaken (by intro y hy; simp only [scratch, List.mem_append, List.mem_cons] at hy ⊢; tauto))

end NearQuarticWires.StagePullback.RightErrors
