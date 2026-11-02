import Proof.Gates.Dispatch.Print

/-!
# Reducing the dyadic rational outputs

Paper: `sec:algorithm`, paper/paper.tex, and `prop:time`. Euclid's binary arithmetic program computes the common
divisor of a nonnegative numerator and its positive denominator. Two exact
divisions produce the canonical natural numerator and denominator.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicGates.Close.Dispatch

def normalNum : Fin VV := ⟨60, by decide⟩
def normalDen : Fin VV := ⟨61, by decide⟩
def reducedNum : Fin VV := ⟨62, by decide⟩
def reducedDen : Fin VV := ⟨63, by decide⟩

def normalizeProgram : St VV :=
  .seq (.op (.copy GCA normalNum)) (.seq (.op (.copy GCB normalDen))
    (.seq gcdv (.seq (assign reducedNum (.div (.var normalNum) (.var GCA)))
      (assign reducedDen (.div (.var normalDen) (.var GCA))))))

def normalScratch : List (Fin VV) := [GCA, GCB, GCQ, GCR, reducedNum, reducedDen, vJ]

theorem normalizeProgram_spec {C : Ctx} (a : DS VV) (hc : Cst a) (N D M : ℕ)
    (hN : a.env normalNum = N) (hD : a.env normalDen = D) (hd : 0 < D)
    (hNM : N ≤ M) (hDM : D ≤ M) (hcap : 2 * M ≤ 2 ^ C.Wd) :
    Hs C normalizeProgram a (14 * (Nat.size N + Nat.size D) + 50) (fun b =>
      b.env reducedNum = N / Nat.gcd N D ∧ b.env reducedDen = D / Nat.gcd N D ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b normalScratch) := by
  have hgpos : 0 < Nat.gcd N D := Nat.gcd_pos_of_pos_right N hd
  have hgle : Nat.gcd N D ≤ M := (Nat.le_of_dvd hd (Nat.gcd_dvd_right N D)).trans hDM
  refine Hx.hs (Hs.then (hs_copy C GCA normalNum a (by decide)) (fun a1 ha1 n1 hn1 => ?_))
  subst ha1
  refine Hs.then (hs_copy C GCB normalDen _ (by decide)) (fun a2 ha2 n2 hn2 => ?_)
  subst ha2
  have hca : Cst ((a.set GCA (a.env normalNum)).set GCB ((a.set GCA (a.env normalNum)).env normalDen)) :=
    (hc.set _ _ (by decide)).set _ _ (by decide)
  refine Hs.then (gcdv_spec _ hca N D M (by vsimp [hN])
    (by vsimp [hD]) hNM hDM hcap)
    (fun b ⟨bg, bp, bw, bo, bc, bf⟩ n3 hn3 => ?_)
  have bN : b.env normalNum = N := by
    rw [bf normalNum (by decide)]
    vsimp [hN]
  have bD : b.env normalDen = D := by
    rw [bf normalDen (by decide)]
    vsimp [hD]
  have bfr : FrS a b normalScratch := by
    have hf0 : Fr a ((a.set GCA (a.env normalNum)).set GCB
        ((a.set GCA (a.env normalNum)).env normalDen)) normalScratch :=
      Fr.trans (Fr.set a (x := GCA) _ (by decide)) (Fr.set _ (x := GCB) _ (by decide))
    exact FrS.trans hf0.toS (bf.toS.weaken (by decide))
  refine Hs.then (assign_spec reducedNum (by decide) (by decide) (.div (.var normalNum) (.var GCA))
    b (by norm_num [AE.vars_ok, normalNum, GCA, vJ]) (by decide) bc (by
      change True ∧ True ∧ 0 < b.env GCA ∧ 2 * b.env GCA ≤ _
      rw [bg]; exact ⟨trivial, trivial, hgpos, by omega⟩))
    (fun d ⟨dq, df, dp, dw, dout, dc⟩ n4 hn4 => ?_)
  have dD : d.env normalDen = D := by rw [df normalDen (by decide) (by decide) (by decide), bD]
  have dg : d.env GCA = Nat.gcd N D := by rw [df GCA (by decide) (by decide) (by decide), bg]
  refine Hs.last (assign_spec reducedDen (by decide) (by decide) (.div (.var normalDen) (.var GCA))
    d (by norm_num [AE.vars_ok, normalDen, GCA, vJ]) (by decide) dc (by
      change True ∧ True ∧ 0 < d.env GCA ∧ 2 * d.env GCA ≤ _
      rw [dg]; exact ⟨trivial, trivial, hgpos, by omega⟩)) ?_
  rintro e ⟨eq, ef, ep, ew, eo, ec⟩ n5 hn5
  refine ⟨⟨?_, ?_, by rw [ep, dp, bp]; rfl, by rw [ew, dw, bw]; rfl,
    by rw [eo, dout, bo]; rfl, ec, ?_⟩, ?_⟩
  · rw [ef reducedNum (by decide) (by decide) (by decide), dq]
    simp only [AE.eval, bN, bg]
  · rw [eq]
    simp only [AE.eval, dD, dg]
  · exact FrS.trans bfr (FrS.trans (df.toS _ (by decide) (by decide)) (ef.toS _ (by decide) (by decide)))
  · simp only [AE.cost] at hn4 hn5
    omega

end NearQuarticWires.StageOutput
