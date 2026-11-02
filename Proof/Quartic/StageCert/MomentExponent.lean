import Proof.Quartic.StageCert.MaskParameters

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `eq:testX`–`eq:testPhi` and `lem:print`, paper/paper.tex: the literal even moment exponent is kept
outside the original coefficient and atom-index scratch. -/
def momentExponent : Fin VV := ⟨115,by decide⟩

/-- `eq:testX`, paper/paper.tex: compute the
population exponent from the actual retained selection width. -/
def preparePopulationExponent : St VV MM :=
  .seq (.op (.copy momentExponent selectionStart)) (.op (.shl momentExponent))

/-- `eq:testX`, `lem:print` and `prop:time`, paper/paper.tex: the original exponent 2k is
obtained by one physical copy and binary shift. -/
theorem preparePopulationExponent_run (C : Ctx) (k : ℕ)
    (a : DS VV MM) (hc : Cst a) (hk : a.env selectionStart=k) (hfit : 2*k<2^C.Wd) :
    Hs C preparePopulationExponent a 3 (fun z=>z.env momentExponent=2*k ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [momentExponent]) := by
  unfold preparePopulationExponent
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C momentExponent selectionStart a (by decide)) ?_
  rintro b rfl
  refine (hs_shl C momentExponent _ (by change 2*a.env selectionStart<2^C.Wd; rw [hk]; exact hfit)).mono le_rfl ?_
  rintro z rfl
  exact ⟨by change 2*a.env selectionStart=2*k; rw [hk],rfl,
    Cst.of_fr (T := [momentExponent]) hc
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))) (by decide),
    (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩

/-- `eq:testE` and `eq:testPhi`, paper/paper.tex:
the fixed m=4 walk exponent is obtained by two further exact shifts. -/
def prepareWalkExponent : St VV MM :=
  .seq preparePopulationExponent (.seq (.op (.shl momentExponent)) (.op (.shl momentExponent)))

/-- `eq:testE`, `eq:testPhi`, `lem:print` and `prop:time`,
paper/paper.tex: the
complete walk exponent 8k is computed by seven bounded source operations. -/
theorem prepareWalkExponent_run (C : Ctx) (k : ℕ)
    (a : DS VV MM) (hc : Cst a) (hk : a.env selectionStart=k) (hfit : 8*k<2^C.Wd) :
    Hs C prepareWalkExponent a 7 (fun z=>z.env momentExponent=8*k ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [momentExponent]) := by
  unfold prepareWalkExponent
  refine Hs.seq (t1 := 3) (t2 := 3)
    (preparePopulationExponent_run C k a hc hk (by omega)) ?_
  rintro b ⟨be,bs,bc,bfr⟩
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_shl C momentExponent b (by rw [be]; omega)) ?_
  rintro d rfl
  refine (hs_shl C momentExponent _ (by change 2*(2*b.env momentExponent)<2^C.Wd; rw [be]; omega)).mono le_rfl ?_
  rintro z rfl
  exact ⟨by change 2*(2*b.env momentExponent)=8*k; rw [be]; omega,bs,
    Cst.of_fr (T := [momentExponent]) bc
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))) (by decide),
    bfr.trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))⟩

end NearQuarticWires.StageCert.Tokens
