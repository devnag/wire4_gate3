import Proof.Quartic.StageRecovery.ModToken

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: all seven literal
postfix tags occupy at most three binary bits. -/
theorem tagOf_bits (token : Tok) : natBitLength (tagOf token) ≤ 3 := by
  cases token <;> norm_num [tagOf, natBitLength]

/-- `lem:print`, paper/paper.tex: one complete token
transition includes its parsed tag and literal payload bytes. -/
def TokenPost (a : DS VV MM) (q point : ℕ) (xs : List ℕ) (token : Tok)
    (b : DS VV MM) : Prop :=
  b.env stackVar = senc q ((modAlg q point).step xs token) ∧
  b.env modulusVar = q ∧ b.ip = a.ip + (tokWord token).length ∧
  (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
    (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b evalScratch

/-- `lem:print`, paper/paper.tex: actual tag parsing,
physical dispatch and bounded modular arithmetic implement one exact
postfix token on the original formula codec. -/
theorem modularToken_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q point : ℕ) (xs : List ℕ) (token : Tok) (rest : List Bool) (B : ℕ)
    (hq : 2 ≤ q) (haq : a.env modulusVar = q) (hap : a.env pointVar = point)
    (hstack : a.env stackVar = senc q xs) (hxs : ∀ x ∈ xs, x < q)
    (hdepth : q ^ (xs.length + 3) ≤ 2 ^ C.Wd)
    (hin : C.inp.drop a.ip = tokWord token ++ rest)
    (hB : tokenBound token ≤ B) (hwidth : B + 5 ≤ C.Wd) :
    Hs C modularToken a (500 * (B + 10)) (TokenPost a q point xs token) := by
  have hbits := tagOf_bits token
  have htag := tagOf_lt token
  have er := readVariable_spec C a hc tagVar (by decide) (by decide) (tagOf token) _
    (by simpa only [tokWord_eq, List.append_assoc] using hin) (by omega)
  unfold modularToken
  refine (Hs.seq (t2 := 100 * B + 3 * tagOf token + 201) er
    fun b ⟨hbt, hbi, hbr, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  let base := b.set tagVar 0
  have hbasec : Cst base := Cst.of_fr (T := [tagVar]) hbc (Fr.set _ _ (by decide)) (by decide)
  have hbaseq : base.env modulusVar = q := by
    rw [DS.set_env_ne _ _ (by decide), hbf _ (by decide), haq]
  have hbasep : base.env pointVar = point := by
    rw [DS.set_env_ne _ _ (by decide), hbf _ (by decide), hap]
  have hbases : base.env stackVar = senc q xs := by
    rw [DS.set_env_ne _ _ (by decide), hbf _ (by decide), hstack]
  have hbasein : C.inp.drop base.ip = payload token ++ rest := by
    change C.inp.drop b.ip = _
    rw [hbi, ← List.drop_drop, hin, tokWord_eq, List.append_assoc, List.drop_left]
  refine (tokenDispatch_spec C modularHandlers (tagOf token)
    (by simpa only [modularHandlers, List.length_cons, List.length_nil] using tagOf_lt token)
    b hbc hbt (100 * B + 200) (TokenPost a q point xs token) ?_).mono (by omega) (fun _ h => h)
  refine (modularPayload_spec C base hbasec q point xs token rest B hq hbaseq hbasep
    hbases hxs hdepth hbasein hB (by omega)).mono le_rfl ?_
  rintro d ⟨hds, hdq, hdi, hdr, hdc, hdf⟩
  refine ⟨hds, hdq, ?_, hdr.trans hbr, hdc, ?_⟩
  · rw [hdi]
    change b.ip + _ = _
    rw [hbi, tokWord_eq, List.length_append]
    omega
  · exact Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) hdf)

end NearQuarticWires.StageRecovery
