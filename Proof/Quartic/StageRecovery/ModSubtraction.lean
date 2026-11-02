import Proof.Quartic.StageRecovery.ModUnary

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells NearCubicGates.Close.Expand

/-- `lem:print`, paper/paper.tex: subtraction of two
reduced postfix operands retains the literal left/right order. -/
def subtractResidue (q left right : ℕ) : ℕ := (left + (q - right)) % q

/-- `lem:print`, paper/paper.tex: the subtraction token
uses modular negation followed by reduced addition on the actual stack. -/
def subtractionModHandler : St VV MM :=
  .seq (popModStack rightVar) (.seq (popModStack leftVar)
    (.seq (negateModProgram rightVar) (.seq addModProgram pushModStack)))

/-- `lem:print`, paper/paper.tex: the complete physical
subtraction token preserves the remainder of the binary postfix stack. -/
theorem subtractionModHandler_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q : ℕ) (xs : List ℕ) (hq : 2 ≤ q) (hxs : ∀ x ∈ xs, x < q)
    (haq : a.env modulusVar = q) (hstack : a.env stackVar = senc q xs)
    (hdepth : q ^ (xs.length + 2) ≤ 2 ^ C.Wd) :
    Hs C subtractionModHandler a 27 (fun b =>
      b.env stackVar = senc q (subtractResidue q (xs.tail.headD 0) (xs.headD 0) :: xs.tail.tail) ∧
      b.env modulusVar = q ∧ b.sh = a.sh ∧ Cst b ∧
      Fr a b [stackVar, leftVar, rightVar, productVar, quotientVar, remainderVar]) := by
  obtain ⟨_, h2q, _, hnew⟩ := depth_facts xs hq hdepth
  have hr : xs.headD 0 < q := Alg.headD_lt (by omega) xs hxs
  have htail := Alg.tail_lt xs hxs
  have hl : xs.tail.headD 0 < q := Alg.headD_lt (by omega) xs.tail htail
  have hres : subtractResidue q (xs.tail.headD 0) (xs.headD 0) < q := Nat.mod_lt _ (by omega)
  have hpush : senc q (subtractResidue q (xs.tail.headD 0) (xs.headD 0) :: xs.tail.tail) < 2 ^ C.Wd :=
    hnew _ (by simp; omega) (by
      intro value hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hres
      · exact Alg.tail_lt xs.tail htail value hv)
  unfold subtractionModHandler
  refine Hs.seq (t2 := 23) (popModStack_spec C a rightVar (by decide) q xs
    (by omega) hxs haq hstack h2q) fun b ⟨hbr, hbs, hbsh, hbf⟩ => ?_
  have hbq : b.env modulusVar = q := by rw [hbf _ (by decide), haq]
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  refine Hs.seq (t2 := 19) (popModStack_spec C b leftVar (by decide) q xs.tail
    (by omega) htail hbq hbs h2q) fun d ⟨hdl, hds, hdsh, hdf⟩ => ?_
  have hdr : d.env rightVar = xs.headD 0 := by rw [hdf _ (by decide), hbr]
  have hdq : d.env modulusVar = q := by rw [hdf _ (by decide), hbq]
  have hdc : Cst d := Cst.of_fr hbc hdf (by decide)
  refine Hs.seq (t2 := 11) (negateModProgram_spec C d rightVar (by decide)
    (by rw [hdq]; omega) (by rw [hdq]; exact h2q)
    (by rw [hdr, hdq]; exact hr.le)) fun e ⟨her, hesh, hef⟩ => ?_
  have hel : e.env leftVar = xs.tail.headD 0 := by rw [hef _ (by decide), hdl]
  have heq : e.env modulusVar = q := by rw [hef _ (by decide), hdq]
  have her' : e.env rightVar = (q - xs.headD 0) % q := by simpa only [hdr, hdq] using her
  have hec : Cst e := Cst.of_fr hdc hef (by decide)
  have hsfit : e.env leftVar + e.env rightVar < 2 ^ C.Wd := by
    rw [hel, her']
    have := Nat.mod_lt (q - xs.headD 0) (by omega : 0 < q)
    omega
  refine Hs.seq (t2 := 5) (addModProgram_spec C e (by rw [heq]; omega)
    (by rw [heq]; exact h2q) hsfit) fun f ⟨hfl, hfsh, hff⟩ => ?_
  have hfl' : f.env leftVar = subtractResidue q (xs.tail.headD 0) (xs.headD 0) := by
    simpa only [hel, her', heq, subtractResidue, Nat.add_mod_mod] using hfl
  have hfq : f.env modulusVar = q := by rw [hff _ (by decide), heq]
  have hfs : f.env stackVar = senc q xs.tail.tail := by
    rw [hff _ (by decide), hef _ (by decide), hds]
  have hfc : Cst f := Cst.of_fr hec hff (by decide)
  refine (pushModStack_spec C f q _ xs.tail.tail hfq hfl' hfs hpush).mono le_rfl ?_
  rintro g ⟨hgs, hgsh, hgf⟩
  exact ⟨hgs, by rw [hgf _ (by decide), hfq],
    hgsh.trans (hfsh.trans (hesh.trans (hdsh.trans hbsh))), Cst.of_fr hfc hgf (by decide),
      Fr.trans (Fr.weaken hbf (by decide)) (Fr.trans (Fr.weaken hdf (by decide))
        (Fr.trans (Fr.weaken hef (by decide)) (Fr.trans (Fr.weaken hff (by decide))
          (Fr.weaken hgf (by decide)))))⟩

end NearQuarticWires.StageRecovery
