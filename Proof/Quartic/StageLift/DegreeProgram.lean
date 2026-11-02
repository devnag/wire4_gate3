import Proof.Gates.Cells.Load2
import Proof.Quartic.StageLift.ResidueBounds

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: a distinct binary degree-header field. -/
def degreeVar : Fin VV := 56

/-- `lem:print`, paper/paper.tex: a distinct binary degree-header field. -/
def degreeExponent : Fin VV := 58

/-- `lem:print`, paper/paper.tex: a distinct binary degree-header field. -/
def degreeChain : Fin VV := 59

/-- `lem:print`, paper/paper.tex: a distinct binary degree-header field. -/
def degreeInput : Fin VV := 61

/-- `lem:print`, paper/paper.tex: a distinct binary degree-header field. -/
def degreeFactor : Fin VV := 62

/-- `lem:print`, paper/paper.tex: a distinct binary degree-header field. -/
def degreePrime : Fin VV := 63

/-- `lem:print`, paper/paper.tex: a distinct binary degree-header field. -/
def degreeTerm : Fin VV := 64

/-- `lem:print`, paper/paper.tex: a distinct binary degree-header field. -/
def degreeProduct : Fin VV := 65

/-- `lem:print`, paper/paper.tex: compute the literal degree header by actual integer instructions. -/
def computeResidueDegree : St VV MM :=
  .seq (setK degreeFactor 16) (.seq (.op (.mul degreeInput degreeFactor degreeVar)) (.seq (.op (.copy degreeFactor degreeExponent)) (.seq (.op (.shl degreeFactor)) (.seq (.op (.sub degreeFactor v1)) (.seq (.op (.copy degreeTerm degreeChain)) (.seq (.op (.inc degreeTerm)) (.seq (.op (.shl degreeTerm)) (.seq (.op (.mul degreeFactor degreeTerm degreeProduct)) (.seq (.op (.copy degreeTerm degreePrime)) (.seq (.op (.sub degreeTerm v1)) (.seq (.op (.mul degreeProduct degreeTerm degreeInput)) (.op (.add degreeVar degreeInput)))))))))))))

/-- `lem:print`, paper/paper.tex: every intermediate of the exact degree calculation fits the stated binary workspace. -/
theorem computeResidueDegree_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (X e J prime : ℕ) (he : 1 ≤ e) (hJ : 1 ≤ J) (hp : 2 ≤ prime)
    (hX : a.env degreeInput = X) (heE : a.env degreeExponent = e)
    (hJJ : a.env degreeChain = J) (hpP : a.env degreePrime = prime)
    (hroom : 16 * X + (2 * e - 1) * (2 * (J + 1)) * prime +
      2 * e + 2 * (J + 1) + prime + 17 < 2 ^ C.Wd) :
    Hs C computeResidueDegree a 100 (fun b =>
      b.env degreeVar = 16 * X + (2 * e - 1) * (2 * (J - 1 + 2)) * (prime - 1) ∧
      b.sh = a.sh ∧ Cst b ∧
      Fr a b [degreeVar, degreeInput, degreeFactor, degreeTerm, degreeProduct, vJ]) := by
  have hprodle : (2 * e - 1) * (2 * (J + 1)) ≤
      (2 * e - 1) * (2 * (J + 1)) * prime := Nat.le_mul_of_pos_right _ (by omega)
  have htermle := Nat.mul_le_mul_left ((2 * e - 1) * (2 * (J + 1))) (Nat.sub_le prime 1)
  have hprod : (2 * e - 1) * (2 * (J + 1)) < 2 ^ C.Wd := by omega
  have hterm : (2 * e - 1) * (2 * (J + 1)) * (prime - 1) < 2 ^ C.Wd := by omega
  have htotal : 16 * X + (2 * e - 1) * (2 * (J + 1)) * (prime - 1) < 2 ^ C.Wd := by omega
  unfold computeResidueDegree
  apply Hx.hs
  refine Hs.then (setK_spec degreeFactor (by decide) 16 a (by omega))
    (fun s0 ⟨h16, hs0, hf0⟩ n0 hn0 => ?_)
  have hinput : s0.env degreeInput = X := (hf0 _ (by decide)).trans hX
  have hexp : s0.env degreeExponent = e := (hf0 _ (by decide)).trans heE
  have hchain : s0.env degreeChain = J := (hf0 _ (by decide)).trans hJJ
  have hprime : s0.env degreePrime = prime := (hf0 _ (by decide)).trans hpP
  have hone : s0.env v1 = 1 := (hf0 _ (by decide)).trans hc.one
  refine Hs.then (hs_mul C degreeInput degreeFactor degreeVar s0 (by decide) (by decide) (by decide) (by vsimp [hinput, h16]; omega))
    (fun z hz n1 hn1 => ?_)
  subst z
  let s1 := s0.set degreeVar (s0.env degreeInput * s0.env degreeFactor)
  refine Hs.then (hs_copy C degreeFactor degreeExponent s1 (by decide))
    (fun z hz n2 hn2 => ?_)
  subst z
  let s2 := s1.set degreeFactor (s1.env degreeExponent)
  refine Hs.then (hs_shl C degreeFactor s2 (by dsimp only [s1, s2]; vsimp [hexp]; omega))
    (fun z hz n3 hn3 => ?_)
  subst z
  let s3 := s2.set degreeFactor (2 * s2.env degreeFactor)
  refine Hs.then (hs_sub C degreeFactor v1 s3 (by decide) (by dsimp only [s1, s2, s3]; vsimp [hexp, hone]; omega))
    (fun z hz n4 hn4 => ?_)
  subst z
  let s4 := s3.set degreeFactor (s3.env degreeFactor - s3.env v1)
  refine Hs.then (hs_copy C degreeTerm degreeChain s4 (by decide))
    (fun z hz n5 hn5 => ?_)
  subst z
  let s5 := s4.set degreeTerm (s4.env degreeChain)
  refine Hs.then (hs_inc C degreeTerm s5 (by dsimp only [s1, s2, s3, s4, s5]; vsimp [hchain]; omega))
    (fun z hz n6 hn6 => ?_)
  subst z
  let s6 := s5.set degreeTerm (s5.env degreeTerm + 1)
  refine Hs.then (hs_shl C degreeTerm s6 (by dsimp only [s1, s2, s3, s4, s5, s6]; vsimp [hchain]; omega))
    (fun z hz n7 hn7 => ?_)
  subst z
  let s7 := s6.set degreeTerm (2 * s6.env degreeTerm)
  refine Hs.then (hs_mul C degreeFactor degreeTerm degreeProduct s7 (by decide) (by decide) (by decide) (by dsimp only [s1, s2, s3, s4, s5, s6, s7]; vsimp [hexp, hchain, hone]; exact hprod))
    (fun z hz n8 hn8 => ?_)
  subst z
  let s8 := s7.set degreeProduct (s7.env degreeFactor * s7.env degreeTerm)
  refine Hs.then (hs_copy C degreeTerm degreePrime s8 (by decide))
    (fun z hz n9 hn9 => ?_)
  subst z
  let s9 := s8.set degreeTerm (s8.env degreePrime)
  refine Hs.then (hs_sub C degreeTerm v1 s9 (by decide) (by dsimp only [s1, s2, s3, s4, s5, s6, s7, s8, s9]; vsimp [hprime, hone]; omega))
    (fun z hz n10 hn10 => ?_)
  subst z
  let s10 := s9.set degreeTerm (s9.env degreeTerm - s9.env v1)
  refine Hs.then (hs_mul C degreeProduct degreeTerm degreeInput s10 (by decide) (by decide) (by decide) (by dsimp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]; vsimp [hexp, hchain, hprime, hone]; exact hterm))
    (fun z hz n11 hn11 => ?_)
  subst z
  let s11 := s10.set degreeInput (s10.env degreeProduct * s10.env degreeTerm)
  refine Hs.last (hs_add C degreeVar degreeInput s11 (by decide) (by dsimp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]; vsimp [hinput, h16, hexp, hchain, hprime, hone]; simpa [Nat.mul_comm] using htotal))
    (fun z hz n12 hn12 => ?_)
  subst z
  let s12 := s11.set degreeVar (s11.env degreeVar + s11.env degreeInput)
  have hf : Fr a s12 [degreeVar, degreeInput, degreeFactor, degreeTerm, degreeProduct, vJ] := by
    apply (hf0.weaken (by simp)).trans
    exact (Fr.set s0 _ (by simp)).trans ((Fr.set s1 _ (by simp)).trans ((Fr.set s2 _ (by simp)).trans ((Fr.set s3 _ (by simp)).trans ((Fr.set s4 _ (by simp)).trans ((Fr.set s5 _ (by simp)).trans ((Fr.set s6 _ (by simp)).trans ((Fr.set s7 _ (by simp)).trans ((Fr.set s8 _ (by simp)).trans ((Fr.set s9 _ (by simp)).trans ((Fr.set s10 _ (by simp)).trans (Fr.set s11 _ (by simp))))))))))))
  refine ⟨⟨?_, ?_, Cst.of_fr hc hf (by decide), hf⟩, by omega⟩
  · change s12.env degreeVar = _
    dsimp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12]
    vsimp [hinput, h16, hexp, hchain, hprime, hone]
    have hj : J - 1 + 2 = J + 1 := by omega
    rw [hj]
    ring
  · exact hs0

end NearQuarticWires.StageLift
