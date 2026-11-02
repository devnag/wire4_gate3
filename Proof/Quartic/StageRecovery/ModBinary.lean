import Proof.Quartic.StageRecovery.ModRpn
import Proof.Quartic.StageRecovery.ModStack

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells NearCubicGates.Close.Expand

/-- `lem:print`, paper/paper.tex: the reduced result of
one binary postfix operation, retaining the literal operand order. -/
def binaryResidue (multiply : Bool) (q left right : ℕ) : ℕ :=
  if multiply then left * right % q else (left + right) % q

/-- `lem:print`, paper/paper.tex: an actual binary
postfix instruction pops both residues, reduces its result, and pushes
the result onto the unchanged remainder of the stack. -/
def binaryModHandler (multiply : Bool) : St VV MM :=
  .seq (popModStack rightVar) (.seq (popModStack leftVar)
    (.seq (if multiply then multiplyModProgram else addModProgram) pushModStack))

/-- `lem:print`, paper/paper.tex: one physical binary
postfix instruction performs the exact reduced stack transition in a
constant number of charged binary operations. -/
theorem binaryModHandler_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (multiply : Bool) (q : ℕ) (xs : List ℕ) (hq : 2 ≤ q)
    (hxs : ∀ x ∈ xs, x < q) (haq : a.env modulusVar = q)
    (hstack : a.env stackVar = senc q xs) (hdepth : q ^ (xs.length + 2) ≤ 2 ^ C.Wd) :
    Hs C (binaryModHandler multiply) a 19 (fun b =>
      b.env stackVar = senc q (binaryResidue multiply q (xs.tail.headD 0) (xs.headD 0) :: xs.tail.tail) ∧
      b.env modulusVar = q ∧ b.sh = a.sh ∧ Cst b ∧
      Fr a b [stackVar, leftVar, rightVar, productVar, quotientVar, remainderVar]) := by
  obtain ⟨hqq, h2q, _, hnew⟩ := depth_facts xs hq hdepth
  have hright : xs.headD 0 < q := Alg.headD_lt (by omega) xs hxs
  have htail : ∀ x ∈ xs.tail, x < q := Alg.tail_lt xs hxs
  have hleft : xs.tail.headD 0 < q := Alg.headD_lt (by omega) xs.tail htail
  have hsum : xs.tail.headD 0 + xs.headD 0 < 2 ^ C.Wd := by omega
  have hprod : xs.tail.headD 0 * xs.headD 0 < 2 ^ C.Wd :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hleft.le)
      (lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hright (by omega)) hqq)
  have hres : binaryResidue multiply q (xs.tail.headD 0) (xs.headD 0) < q := by
    cases multiply <;> exact Nat.mod_lt _ (by omega)
  unfold binaryModHandler
  refine Hs.seq (t2 := 15) (popModStack_spec C a rightVar (by decide) q xs
    (by omega) hxs haq hstack h2q) fun b ⟨hbr, hbs, hbsh, hbf⟩ => ?_
  have hbq : b.env modulusVar = q := by rw [hbf _ (by decide), haq]
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  refine Hs.seq (t2 := 11) (popModStack_spec C b leftVar (by decide) q xs.tail
    (by omega) htail hbq hbs h2q) fun d ⟨hdl, hds, hdsh, hdf⟩ => ?_
  have hdr : d.env rightVar = xs.headD 0 := by rw [hdf _ (by decide), hbr]
  have hdq : d.env modulusVar = q := by rw [hdf _ (by decide), hbq]
  have hdc : Cst d := Cst.of_fr hbc hdf (by decide)
  have hop : Hs C (if multiply then multiplyModProgram else addModProgram) d 5
      (fun e => e.env leftVar = binaryResidue multiply q (xs.tail.headD 0) (xs.headD 0) ∧
        e.sh = d.sh ∧ Fr d e [leftVar, productVar, quotientVar, remainderVar]) := by
    cases multiply with
    | false =>
        refine (addModProgram_spec C d (by rw [hdq]; omega) (by rw [hdq]; exact h2q)
          (by rw [hdl, hdr]; exact hsum)).mono le_rfl ?_
        rintro e ⟨hel, hesh, hef⟩
        exact ⟨by simpa only [binaryResidue, Bool.false_eq_true, if_false, hdl, hdr, hdq] using hel,
          hesh, Fr.weaken hef (by decide)⟩
    | true =>
        refine (multiplyModProgram_spec C d (by rw [hdq]; omega) (by rw [hdq]; exact h2q)
          (by rw [hdl, hdr]; exact hprod)).mono le_rfl ?_
        rintro e ⟨hel, hesh, hef⟩
        exact ⟨by simpa only [binaryResidue, if_true, hdl, hdr, hdq] using hel, hesh, hef⟩
  refine Hs.seq (t2 := 5) hop fun e ⟨hel, hesh, hef⟩ => ?_
  have heq : e.env modulusVar = q := by rw [hef _ (by decide), hdq]
  have hes : e.env stackVar = senc q xs.tail.tail := by rw [hef _ (by decide), hds]
  have hec : Cst e := Cst.of_fr hdc hef (by decide)
  have hpush : senc q (binaryResidue multiply q (xs.tail.headD 0) (xs.headD 0) :: xs.tail.tail) < 2 ^ C.Wd :=
    hnew _ (by simp; omega) (by
      intro value hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hres
      · exact Alg.tail_lt xs.tail htail value hv)
  refine (pushModStack_spec C e q _ xs.tail.tail heq hel hes hpush).mono le_rfl ?_
  rintro f ⟨hfs, hfsh, hff⟩
  refine ⟨hfs, by rw [hff _ (by decide), heq],
    hfsh.trans (hesh.trans (hdsh.trans hbsh)), Cst.of_fr hec hff (by decide), ?_⟩
  exact Fr.trans (Fr.weaken hbf (by decide))
    (Fr.trans (Fr.weaken hdf (by decide))
      (Fr.trans (Fr.weaken hef (by decide)) (Fr.weaken hff (by decide))))

end NearQuarticWires.StageRecovery
