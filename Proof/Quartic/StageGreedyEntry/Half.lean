import Proof.Wire_3_5.PrimTC4Geo
import Proof.Wire_3_5.FinalPassWords

/-!
# The dense width from the original arity

Paper: `imp:partition` and `lem:print`, paper/paper.tex.

The star partition has an even number `r` of blocks of length `b` with `r·b ≤ n`; its dense width
`(r/2)·b + ⌈(n−rb)/2⌉` therefore equals `⌈n/2⌉ = (n+1)/2` (`width_eq`). `halfP` halves a counter
(`halfP_exec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `imp:partition`, paper/paper.tex: the dense width is `⌈n/2⌉`. -/
theorem width_eq (P : StarParams) : PrimT.C4Geo.width P=(P.n+1)/2 := by
  have h1:=P.r_mul_b_le
  obtain ⟨k,hk⟩:=P.r_even
  unfold PrimT.C4Geo.width PrimT.C4Geo.hL
  rw [hk] at h1 ⊢
  have e1 : (k+k)/2=k := by omega
  have e2 : (k+k)*P.b=2*(k*P.b) := by ring
  rw [e1,e2]
  rw [e2] at h1
  omega

variable {ns nr : ℕ} (cap : ℕ)

/-- `lem:print`, paper/paper.tex: `H += K/2`, `K := 0`. -/
def halfP (K H : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (.ifr K (.seq (.dec K) (.inc H)) .skip))

theorem halfP_exec (K H : Fin nr) (hKH : K≠H) :
    ∀ (m h : ℕ) (σ : WState ns nr),σ.val K=m → σ.val H=h → m≤cap → h+m/2<cap+1 →
      WExec cap (halfP K H) σ ((σ.setv K 0).setv H (h+m/2)) (6*m+1)
  | 0,h,σ,hK,hH,_,_=>by
    have e : (σ.setv K 0).setv H (h+0/2)=σ := by
      refine WState.eq rfl rfl ?_ rfl
      funext x
      by_cases x1 : x=H
      · subst x1;simp [hH]
      · by_cases x2 : x=K
        · subst x2;simp [Function.update_of_ne x1,hK]
        · simp [Function.update_of_ne x1,Function.update_of_ne x2]
    rw [e]
    exact WExec.whrF hK
  | 1,h,σ,hK,hH,_,_=>by
    have d1:=WExec.dec (cap:=cap) K σ (by omega)
    set σ1:=σ.setv K (σ.val K-1) with hσ1
    have k1 : σ1.val K=0 := by simp [hσ1,hK]
    have i1 : WExec cap (.ifr K (.seq (.dec K) (.inc H)) .skip) σ1 σ1 1 :=
      WExec.ifrF k1 (WExec.skip σ1)
    have w1 : WExec cap (halfP K H) σ1 σ1 1 := WExec.whrF k1
    have e : (σ.setv K 0).setv H (h+1/2)=σ1 := by
      refine WState.eq rfl rfl ?_ rfl
      funext x
      by_cases x1 : x=H
      · subst x1;simp [hσ1,Function.update_of_ne hKH.symm,hH]
      · by_cases x2 : x=K
        · subst x2;simp [hσ1,Function.update_of_ne x1,hK]
        · simp [hσ1,Function.update_of_ne x1,Function.update_of_ne x2]
    rw [e]
    exact WExec.mono (WExec.whrT (by omega) (WExec.seq d1 i1) w1) (by omega)
  | m+2,h,σ,hK,hH,hm,hc=>by
    have d1:=WExec.dec (cap:=cap) K σ (by omega)
    set σ1:=σ.setv K (σ.val K-1) with hσ1
    have k1 : σ1.val K=m+1 := by simp [hσ1,hK]
    have d2:=WExec.dec (cap:=cap) K σ1 (by omega)
    set σ2:=σ1.setv K (σ1.val K-1) with hσ2
    have k2 : σ2.val K=m := by simp [hσ2,k1]
    have h2 : σ2.val H=h := by simp [hσ2,hσ1,Function.update_of_ne hKH.symm,hH]
    have c2 : σ2.val H<cap := by
      rw [h2]
      have : (m+2)/2=m/2+1 := by omega
      omega
    have n2:=WExec.inc (cap:=cap) H σ2 c2
    set σ3:=σ2.setv H (σ2.val H+1) with hσ3
    have i1 : WExec cap (.ifr K (.seq (.dec K) (.inc H)) .skip) σ1 σ3 6 :=
      WExec.ifrT (by omega) (WExec.seq d2 n2)
    have ih:=halfP_exec K H hKH m (h+1) σ3 (by simp [hσ3,Function.update_of_ne hKH,k2])
      (by simp [hσ3,h2]) (by omega) (by
        have : (m+2)/2=m/2+1 := by omega
        omega)
    have e : (σ3.setv K 0).setv H (h+1+m/2)=(σ.setv K 0).setv H (h+(m+2)/2) := by
      have : (m+2)/2=m/2+1 := by omega
      refine WState.eq rfl rfl ?_ rfl
      funext x
      by_cases x1 : x=H
      · subst x1;simp;omega
      · by_cases x2 : x=K
        · subst x2;simp [Function.update_of_ne x1]
        · simp [hσ3,hσ2,hσ1,Function.update_of_ne x1,Function.update_of_ne x2]
    rw [e] at ih
    exact WExec.mono (WExec.whrT (by omega) (WExec.seq d1 i1) ih) (by omega)

end NearQuarticWires.StageGreedyEntry
