import Proof.Quartic.StageRecovery.ModLoop

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the literal evaluator
retains every store, output, callee buffer and non-input cursor. -/
def formulaRest (a : DS VV MM) := (a.out, a.ram, a.rc, a.kin, a.kout, a.kc)

/-- `lem:print`, paper/paper.tex: the complete literal
token stream is evaluated by an actual sequential binary program with
the exact general-modulus postfix semantics and linear token count. -/
theorem modularTokenLoop_suffix_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q point : ℕ) (tokens : List Tok) (suffix : List Bool) (B : ℕ) (hq : 2 ≤ q)
    (haq : a.env modulusVar = q) (hap : a.env pointVar = point)
    (hstack : a.env stackVar = 0) (hcount : a.env tokenCountVar = tokens.length)
    (hcountfit : tokens.length < 2 ^ C.Wd)
    (hin : C.inp.drop a.ip = tokenStream tokens ++ suffix)
    (hbound : ∀ token ∈ tokens, tokenBound token ≤ B) (hwidth : B + 5 ≤ C.Wd)
    (hdepth : q ^ (tokens.length + 3) ≤ 2 ^ C.Wd) :
    Hs C modularTokenLoop a (tokens.length * (500 * (B + 10) + 4) + 4) (fun b =>
      b.env stackVar = senc q (tokens.foldl (modAlg q point).step []) ∧
      b.env modulusVar = q ∧ b.env pointVar = point ∧
      b.ip = a.ip + (tokenStream tokens).length ∧ formulaRest b = formulaRest a ∧ Cst b ∧
      Fr a b (tokenCounterVar :: evalScratch)) := by
  let A := modAlg q point
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env stackVar = senc q ((tokens.take k).foldl A.step []) ∧
      b.env modulusVar = q ∧ b.env pointVar = point ∧
      b.ip = a.ip + (tokenStream (tokens.take k)).length ∧ formulaRest b = formulaRest a ∧ Cst b ∧
      Fr a b (tokenCounterVar :: evalScratch)
  unfold modularTokenLoop
  refine (forS_spec' tokenCounterVar tokenCountVar (by decide) modularToken a tokens.length
    hcountfit I (500 * (B + 10)) (fun k b value ⟨hs, hq', hp, hi, ho, hbc, hbf⟩ => ?_)
    ⟨by simpa [senc] using hstack, haq, hap, by simp [tokenStream], rfl, hc, Fr.refl _ _⟩
    hcount ?_).mono le_rfl ?_
  · exact ⟨by simpa (config := {decide := true}) [DS.set] using hs,
      by simpa (config := {decide := true}) [DS.set] using hq',
      by simpa (config := {decide := true}) [DS.set] using hp, hi, ho,
      Cst.of_fr (T := [tokenCounterVar]) hbc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans hbf (Fr.set _ _ (by simp))⟩
  · intro k hk b ⟨hs, hbq, hbp, hbi, hbo, hbc, hbf⟩ hctr hcnt
    have hmem : tokens[k] ∈ tokens := List.getElem_mem hk
    have hxs := A.foldl_lt (modAlg_closed q point (by omega)) (tokens.take k)
    have hlocal : q ^ (((tokens.take k).foldl A.step []).length + 3) ≤ 2 ^ C.Wd :=
      (Nat.pow_le_pow_right (by omega)
        (by have := List.length_take_le k tokens; omega)).trans hdepth
    have hinput : C.inp.drop b.ip = tokWord tokens[k] ++ (tokenStream (tokens.drop (k + 1)) ++ suffix) := by
      rw [hbi, ← List.drop_drop, hin]
      have hd : (tokenStream tokens).length ≥ (tokenStream (tokens.take k)).length := by
        have he := congrArg tokenStream (List.take_append_drop k tokens)
        simp only [tokenStream, List.flatMap_append] at he
        change (tokens.flatMap tokWord).length ≥ ((tokens.take k).flatMap tokWord).length
        rw [← he, List.length_append]
        omega
      rw [List.drop_append_of_le_length hd, tokenStream_drop tokens k hk, List.append_assoc]
    refine (modularToken_spec C b hbc q point _ tokens[k] _ B hq hbq hbp hs hxs.1
      hlocal hinput (hbound _ hmem) hwidth).mono le_rfl ?_
    rintro d ⟨hds, hdq, hdi, hdr, hdc, hdf⟩
    have hstream : tokenStream (tokens.take (k + 1)) =
        tokenStream (tokens.take k) ++ tokWord tokens[k] := by
      have he := congrArg tokenStream (List.take_succ_eq_append_getElem hk)
      simpa only [tokenStream, List.flatMap_append, List.flatMap_singleton] using he
    refine ⟨⟨?_, hdq, by rw [hdf _ (by decide), hbp], ?_,
      hdr.trans hbo, hdc,
      Fr.trans hbf (Fr.weaken hdf (by intro y hy; exact List.mem_cons_of_mem _ hy))⟩,
      by rw [hdf _ (by decide), hctr], by rw [hdf _ (by decide), hcnt]⟩
    · rw [hds, List.take_succ_eq_append_getElem hk, List.foldl_append]
      rfl
    · rw [hdi, hbi, hstream, List.length_append]
      omega
  · rintro b ⟨hb, _, _⟩
    simpa only [I, A, List.take_length] using hb


end NearQuarticWires.StageRecovery
