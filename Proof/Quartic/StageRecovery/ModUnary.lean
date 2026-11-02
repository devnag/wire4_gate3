import Proof.Quartic.StageRecovery.ModBinary
import Proof.Quartic.StageRecovery.ModNegate
import Proof.Quartic.StageRecovery.ModPower

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells NearCubicGates.Close.Expand

/-- `lem:print`, paper/paper.tex: the exact reduced
stack transition for a unary arithmetic token. -/
def unaryResidue (power : Bool) (q exponent value : ℕ) : ℕ :=
  if power then value ^ exponent % q else (q - value) % q

/-- `lem:print`, paper/paper.tex: a unary postfix
operation physically pops, computes and pushes one reduced residue. -/
def unaryModHandler (power : Bool) : St VV MM :=
  if power then .seq (popModStack rightVar) (.seq powerModProgram pushModStack)
  else .seq (popModStack leftVar) (.seq (negateModProgram leftVar) pushModStack)

/-- `lem:print`, paper/paper.tex: every unary modular
postfix instruction preserves the remaining actual binary stack and
all retained formula metadata outside the stated work variables. -/
theorem unaryModHandler_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (power : Bool) (q exponent : ℕ) (xs : List ℕ) (hq : 2 ≤ q)
    (hxs : ∀ x ∈ xs, x < q) (haq : a.env modulusVar = q)
    (hae : power = true → a.env exponentVar = exponent)
    (hexp : power = true → exponent < 2 ^ C.Wd)
    (hstack : a.env stackVar = senc q xs) (hdepth : q ^ (xs.length + 3) ≤ 2 ^ C.Wd) :
    Hs C (unaryModHandler power) a (if power then exponent * 9 + 22 else 22) (fun b =>
      b.env stackVar = senc q (unaryResidue power q exponent (xs.headD 0) :: xs.tail) ∧
      b.env modulusVar = q ∧ b.sh = a.sh ∧ Cst b ∧
      Fr a b [stackVar, leftVar, rightVar, productVar, quotientVar, remainderVar, c0]) := by
  have hshort : q ^ (xs.length + 2) ≤ 2 ^ C.Wd :=
    (Nat.pow_le_pow_right (by omega) (by omega)).trans hdepth
  obtain ⟨hqq, h2q, _, hnew⟩ := depth_facts xs hq hshort
  have hqqstrict : q * q < 2 ^ C.Wd := by
    have hpower : q ^ 3 ≤ 2 ^ C.Wd :=
      (Nat.pow_le_pow_right (by omega) (by omega)).trans hdepth
    nlinarith
  have htop : xs.headD 0 < q := Alg.headD_lt (by omega) xs hxs
  have hres : unaryResidue power q exponent (xs.headD 0) < q := by
    cases power <;> exact Nat.mod_lt _ (by omega)
  have hpush : senc q (unaryResidue power q exponent (xs.headD 0) :: xs.tail) < 2 ^ C.Wd :=
    hnew _ (by simp) (by
      intro value hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hres
      · exact Alg.tail_lt xs hxs value hv)
  cases power with
  | false =>
      unfold unaryModHandler
      refine (Hs.seq (t2 := 13) (popModStack_spec C a leftVar (by decide) q xs
        (by omega) hxs haq hstack h2q) fun b ⟨hbl, hbs, hbsh, hbf⟩ => ?_).mono
          (by simp only [Bool.false_eq_true, if_false]; omega) (fun _ h => h)
      have hbq : b.env modulusVar = q := by rw [hbf _ (by decide), haq]
      have hbc : Cst b := Cst.of_fr hc hbf (by decide)
      refine Hs.seq (t2 := 5) (negateModProgram_spec C b leftVar (by decide)
        (by rw [hbq]; omega) (by rw [hbq]; exact h2q)
        (by rw [hbl, hbq]; exact htop.le)) fun d ⟨hdl, hdsh, hdf⟩ => ?_
      have hdl' : d.env leftVar = unaryResidue false q exponent (xs.headD 0) := by
        simpa only [unaryResidue, Bool.false_eq_true, if_false, hbq, hbl] using hdl
      have hdq : d.env modulusVar = q := by rw [hdf _ (by decide), hbq]
      have hds : d.env stackVar = senc q xs.tail := by rw [hdf _ (by decide), hbs]
      have hdc : Cst d := Cst.of_fr hbc hdf (by decide)
      refine (pushModStack_spec C d q _ xs.tail hdq hdl' hds hpush).mono le_rfl ?_
      rintro e ⟨hes, hesh, hef⟩
      exact ⟨hes, by rw [hef _ (by decide), hdq], hesh.trans (hdsh.trans hbsh),
        Cst.of_fr hdc hef (by decide), Fr.trans (Fr.weaken hbf (by decide))
          (Fr.trans (Fr.weaken hdf (by decide)) (Fr.weaken hef (by decide)))⟩
  | true =>
      unfold unaryModHandler
      refine (Hs.seq (t2 := exponent * 9 + 12)
        (popModStack_spec C a rightVar (by decide) q xs (by omega) hxs haq hstack h2q)
        fun b ⟨hbr, hbs, hbsh, hbf⟩ => ?_).mono (by simp only [if_true]; omega) (fun _ h => h)
      have hbq : b.env modulusVar = q := by rw [hbf _ (by decide), haq]
      have hbe : b.env exponentVar = exponent := by rw [hbf _ (by decide), hae rfl]
      have hbc : Cst b := Cst.of_fr hc hbf (by decide)
      refine (Hs.seq (t2 := 5) (powerModProgram_spec C b hbc q (xs.headD 0) exponent hq htop
        hbq hbr hbe (hexp rfl) h2q hqqstrict) fun d ⟨hdl, _, hdq, hdsh, hdc, hdf⟩ => ?_).mono
          (by omega) (fun _ h => h)
      have hds : d.env stackVar = senc q xs.tail := by rw [hdf _ (by decide), hbs]
      refine (pushModStack_spec C d q _ xs.tail hdq hdl hds hpush).mono le_rfl ?_
      rintro e ⟨hes, hesh, hef⟩
      exact ⟨hes, by rw [hef _ (by decide), hdq], hesh.trans (hdsh.trans hbsh),
        Cst.of_fr hdc hef (by decide), Fr.trans (Fr.weaken hbf (by decide))
          (Fr.trans (Fr.weaken hdf (by decide)) (Fr.weaken hef (by decide)))⟩

end NearQuarticWires.StageRecovery
