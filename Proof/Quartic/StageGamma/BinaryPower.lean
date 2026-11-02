import Proof.Quartic.StageGamma.ReplyRead

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: binary
powers of the decoded degree, side exponent and Gaussian nullity are
formed by actual shifts, never by an uncharged numerical assignment. -/
def binaryPower (index count result : Fin VV) : St VV MM :=
  .seq (.op (.copy result v1)) (forS index count (.op (.shl result)))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: exact powers use linearly many binary shifts and preserve
all ORIGINAL fields and cached data outside the two named registers. -/
theorem binaryPower_run (C : Ctx) (index count result : Fin VV)
    (hic : index ≠ count) (hir : index ≠ result) (hcr : count ≠ result)
    (hconstants : vZ ∉ [index, result] ∧ v1 ∉ [index, result] ∧ v2 ∉ [index, result])
    (a : DS VV MM) (hc : Cst a) (N : ℕ) (hcount : a.env count = N) (hN : N < C.Wd) :
    Hs C (binaryPower index count result) a (5 * N + 6) (fun b =>
      b.env result = 2 ^ N ∧ Same a b ∧ Cst b ∧ Fr a b [index, result]) := by
  have hr1 : result ≠ v1 := by intro h; exact hconstants.2.1 (by simp [h])
  have hcS : ∀ {b : DS VV MM}, Cst b → ∀ c,
      Cst (b.set result c) := by
    intro b hb c
    exact Cst.of_fr hb (Fr.set b c (by simp : result ∈ [index, result])) hconstants
  have hcI : ∀ {b : DS VV MM}, Cst b → ∀ c,
      Cst (b.set index c) := by
    intro b hb c
    exact Cst.of_fr hb (Fr.set b c (by simp : index ∈ [index, result])) hconstants
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env result = 2 ^ k ∧ Same a b ∧ Cst b ∧ Fr a b [index, result]
  have hI : ∀ k b v, I k b → I k (b.set index v) := by
    intro k b v ⟨hb, hs, hbc, hfr⟩
    exact ⟨by rw [DS.set_env_ne _ _ hir.symm]; exact hb,
      hs.trans (Same.set _ _ _), hcI hbc v, hfr.trans (Fr.set b v (by simp))⟩
  have h0 : I 0 (a.set result (a.env v1)) :=
    ⟨by simp [hc.one], Same.set _ _ _, hcS hc _, Fr.set a _ (by simp)⟩
  have hfit : N < 2 ^ C.Wd := hN.trans (show C.Wd < 2 ^ C.Wd from Nat.lt_two_pow_self)
  unfold binaryPower
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := N * 5 + 4)
    (hs_copy C result v1 a hr1) ?_) (by omega) (fun _ h => h)
  intro b hb
  subst hb
  refine Hs.mono (forS_spec' index count hic (.op (.shl result))
    (a.set result (a.env v1)) N hfit I 1 hI h0
    (by rw [DS.set_env_ne _ _ hcr]; exact hcount) ?_) le_rfl ?_
  · intro k hk b ⟨hb, hs, hbc, hfr⟩ hindex hcn
    have hp : 2 * b.env result < 2 ^ C.Wd := by
      rw [hb, Nat.mul_comm 2, ← pow_succ]
      exact Nat.pow_lt_pow_right (by decide) (by omega)
    refine Hs.mono (hs_shl C result b hp) le_rfl ?_
    rintro d rfl
    exact ⟨⟨by simp [hb, pow_succ, Nat.mul_comm], hs.trans (Same.set _ _ _),
      hcS hbc _, hfr.trans (Fr.set b _ (by simp))⟩,
      by rw [DS.set_env_ne _ _ hir]; exact hindex,
      by rw [DS.set_env_ne _ _ hcr]; exact hcn⟩
  · rintro b ⟨hi, _, _⟩
    exact hi

end NearQuarticWires.StageGamma
