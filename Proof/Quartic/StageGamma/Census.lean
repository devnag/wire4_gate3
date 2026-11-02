import Proof.Quartic.StageGamma.ChoiceDecode
import Proof.Quartic.StageGamma.Metadata

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: the exact
number of choices is retained independently of the current address. -/
def gammaCensus : Fin VV := ⟨94, by decide⟩

/-- `cor:conditional`, paper/paper.tex: a fixed
temporary binary variable supports the eight census multiplications. -/
def gammaProductTemp : Fin VV := ⟨99, by decide⟩

/-- `cor:conditional`, paper/paper.tex: each census
iteration physically multiplies the current power by the true base Q+1. -/
def censusBody : St VV MM :=
  .seq (.op (.mul gammaCensus gammaBase gammaProductTemp))
    (.op (.copy gammaCensus gammaProductTemp))

/-- `cor:conditional`, paper/paper.tex: the finite
eight-coordinate expansion is counted by its true radix, including Q=0. -/
def prepareCensus : St VV MM :=
  .seq (.op (.copy gammaBase (requestFieldRegister 2)))
    (.seq (.op (.inc gammaBase)) (.seq (.op (.copy gammaCensus v1))
      (forS gammaPowerIndex (requestFieldRegister 5) censusBody)))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: actual binary operations form Q+1 and EXACTLY `(Q+1)^8`,
without a padded field census and with every overflow condition derived. -/
theorem prepareCensus_run (C : Ctx) (request : Machine.GammaRequest)
    (a : DS VV MM) (hc : Cst a)
    (hQ : a.env (requestFieldRegister 2) = request.parameters.Q)
    (h8 : a.env (requestFieldRegister 5) = 8)
    (hwidth : Cycle.seedLength request.parameters + 10 ≤ C.Wd) :
    Hs C prepareCensus a 66 (fun b =>
      b.env gammaBase = request.parameters.Q + 1 ∧
      b.env gammaCensus = (request.parameters.Q + 1) ^ 8 ∧ Same a b ∧ Cst b ∧
      Fr a b [gammaBase, gammaCensus, gammaProductTemp, gammaPowerIndex]) := by
  let base := request.parameters.Q + 1
  let T : List (Fin VV) := [gammaBase, gammaCensus, gammaProductTemp, gammaPowerIndex]
  have hconst : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T := by decide
  have hfit : base ^ 8 < 2 ^ C.Wd :=
    (choiceCount_le request).trans_lt
      (Nat.pow_lt_pow_right (by decide) (by omega))
  have hbfit : base < 2 ^ C.Wd := by
    have hb : base ≤ base ^ 8 := by
      calc
        _ = base ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by dsimp [base]; omega) (by decide)
    omega
  have hnfit : 8 < 2 ^ C.Wd := by
    have hh : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
    omega
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env gammaCensus = base ^ k ∧ b.env gammaBase = base ∧ Same a b ∧ Cst b ∧ Fr a b T
  have hI : ∀ k b v, I k b → I k (b.set gammaPowerIndex v) := by
    intro k b v ⟨hcensus, hb, hs, hbc, hf⟩
    exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hcensus,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hb, hs.trans (Same.set _ _ _),
      Cst.of_fr hbc (Fr.set b v (by simp [T])) hconst,
      hf.trans (Fr.set b v (by simp [T]))⟩
  have hbody : ∀ k < 8, ∀ b, I k b → b.env gammaPowerIndex = k →
      b.env (requestFieldRegister 5) = 8 → Hs C censusBody b 3
        (fun d => I (k + 1) d ∧ d.env gammaPowerIndex = k ∧
          d.env (requestFieldRegister 5) = 8) := by
    intro k hk b ⟨hcensus, hb, hs, hbc, hf⟩ hi hn
    have hmul : b.env gammaCensus * b.env gammaBase < 2 ^ C.Wd := by
      rw [hcensus, hb, ← pow_succ]
      exact (Nat.pow_le_pow_right (by dsimp [base]; omega) (by omega)).trans_lt hfit
    unfold censusBody
    refine Hs.seq (t1 := 1) (t2 := 1)
      (hs_mul C gammaCensus gammaBase gammaProductTemp b (by decide) (by decide) (by decide) hmul) ?_
    intro d hd
    subst hd
    refine Hs.mono (hs_copy C gammaCensus gammaProductTemp _ (by decide)) le_rfl ?_
    rintro e rfl
    have hefr : Fr b ((b.set gammaProductTemp (b.env gammaCensus * b.env gammaBase)).set
      gammaCensus ((b.set gammaProductTemp (b.env gammaCensus * b.env gammaBase)).env gammaProductTemp)) T :=
      (Fr.set b _ (by simp [T])).trans (Fr.set _ _ (by simp [T]))
    exact ⟨⟨by simp [hcensus, hb, pow_succ], by vsimp [hb],
      hs.trans ((Same.set _ _ _).trans (Same.set _ _ _)), Cst.of_fr hbc hefr hconst,
      hf.trans hefr⟩,
      by vsimp [hi], by vsimp [hn]⟩
  unfold prepareCensus
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 64)
    (hs_copy C gammaBase (requestFieldRegister 2) a (by decide)) ?_)
    (by omega) (fun _ h => h)
  intro b hb
  subst hb
  refine Hs.seq (t1 := 1) (t2 := 62)
    (hs_inc C gammaBase _ (by simp [hQ]; exact hbfit)) ?_
  intro b hb
  subst hb
  refine Hs.seq (t1 := 1) (t2 := 60) (hs_copy C gammaCensus v1 _ (by decide)) ?_
  intro b hb
  subst hb
  let b := ((a.set gammaBase (a.env (requestFieldRegister 2))).set gammaBase
    ((a.set gammaBase (a.env (requestFieldRegister 2))).env gammaBase + 1)).set gammaCensus
      (((a.set gammaBase (a.env (requestFieldRegister 2))).set gammaBase
        ((a.set gammaBase (a.env (requestFieldRegister 2))).env gammaBase + 1)).env v1)
  have hf : Fr a b T := (Fr.set a _ (by simp [T])).trans
    ((Fr.set _ _ (by simp [T])).trans (Fr.set _ _ (by simp [T])))
  have hb0 : I 0 b := ⟨by vsimp [b, hc.one], by vsimp [b, hQ, base],
    (Same.set _ _ _).trans ((Same.set _ _ _).trans (Same.set _ _ _)),
    Cst.of_fr hc hf hconst, hf⟩
  refine Hs.mono (forS_spec' gammaPowerIndex (requestFieldRegister 5) (by decide)
    censusBody b 8 hnfit I 3 hI hb0 (by vsimp [b, h8]) hbody) (by norm_num) ?_
  rintro b ⟨⟨hcensus, hb, hs, hbc, hfr⟩, _, _⟩
  exact ⟨hb, hcensus, hs, hbc, hfr⟩

end NearQuarticWires.StageGamma
