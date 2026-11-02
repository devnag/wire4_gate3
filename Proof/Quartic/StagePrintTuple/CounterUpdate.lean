import Proof.Gates.WordPrograms.RegArith

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: one actual
Cartesian step multiplies its genuine child and old tuple counts,
clears the consumed child count and advances the common row stride. -/
def tupleCounterProgram (R : Fin 7↪Fin nr) : WMX ns nr :=
  .seq (mulR (R 0) (R 4) (R 1) (R 5) (R 6))
    (.seq (.wm (WM.clear (R 1)))
      (.seq (.wm (WM.move (R 5) (R 1)))
        (.seq (.wm (WM.clear (R 0))) (addR (R 3) (R 2) (R 6)))))

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact computed tuple product and row stride are
obtained by genuine bounded register operations, including all cleanup.
Zero-child pools and an initially singleton empty tuple are included. -/
theorem tupleCounterProgram_spec (cap : ℕ) (R : Fin 7↪Fin nr) (K T M N : ℕ)
    (σ : WState ns nr) (hK : σ.val (R 0)=K) (hT : σ.val (R 1)=T)
    (hM : σ.val (R 2)=M) (hN : σ.val (R 3)=N)
    (h4 : σ.val (R 4)=0) (h5 : σ.val (R 5)=0) (h6 : σ.val (R 6)=0)
    (hprod : K*T≤cap) (hdouble : 2*K≤cap) (hOld : T≤cap) (hstride : M+N≤cap) :
    WXExec cap (tupleCounterProgram R) σ
      (((σ.setv (R 1) (K*T)).setv (R 0) 0).setv (R 2) (M+N))
      (100*(K*T+K+T+N+1)) := by
  have hr {i j:Fin 7} : R i=R j ↔ i=j := R.injective.eq_iff
  have en := mulR_spec cap (A:=R 0) (A2:=R 4) (B:=R 1) (C:=R 5) (T:=R 6)
    (by simp [hr]) σ h4 h6 (by rw [h5,hK,hT];omega) (by rw [hK];exact hdouble)
  let a := σ.setv (R 5) (K*T)
  have en' : WXExec cap (mulR (R 0) (R 4) (R 1) (R 5) (R 6)) σ a
      (K*(18*T+3+8)+7*K+3) := by simpa [a,h5,hK,hT] using en
  have ec := wclear_spec cap (R 1) T a (by simp [a,hr,hT]) (by simp [a,hr,hT];exact hOld)
  let b := a.setv (R 1) 0
  have em := wmove_spec cap (R 5) (R 1) (R.injective.ne (by decide)) (K*T) b
    (by simp [b,a,hr]) (by simp [b,a,hr];exact hprod) (by simp [b,a,hr];exact hprod)
  let c := (b.setv (R 5) 0).setv (R 1) (K*T)
  have em' : WExec cap (WM.move (R 5) (R 1)) b c (7*(K*T)+1) := by
    simpa [c,b,a,hr] using em
  have ek := wclear_spec cap (R 0) K c (by simp [c,b,a,hr,hK])
    (by simp [c,b,a,hr,hK];omega)
  let d := c.setv (R 0) 0
  have es := addR_spec cap (A:=R 3) (B:=R 2) (T:=R 6)
    (R.injective.ne (by decide)) (R.injective.ne (by decide)) (R.injective.ne (by decide)) d
    (by simp [d,c,b,a,hr,h6]) (by simp [d,c,b,a,hr,hM,hN];exact hstride)
  have es' : WXExec cap (addR (R 3) (R 2) (R 6)) d (d.setv (R 2) (M+N)) (18*N+3) := by
    simpa [d,c,b,a,hr,hM,hN] using es
  refine (en'.seq ((WXExec.wm ec).seq ((WXExec.wm em').seq ((WXExec.wm ek).seq es')))).cast cap ?_ ?_
  · apply WState.eq
    · rfl
    · rfl
    · funext i
      by_cases h1:i=R 1
      · subst i;simp [d,c,b,a,hr]
      · by_cases h0:i=R 0
        · subst i;simp [d,c,b,a,hr]
        · by_cases h2:i=R 2
          · subst i;simp [d,c,b,a,hr]
          · by_cases h5i:i=R 5
            · subst i;simp [d,c,b,a,hr,h5]
            · simp [d,c,b,a,Function.update_of_ne h1,Function.update_of_ne h0,
                Function.update_of_ne h2,Function.update_of_ne h5i]
    · rfl
  · nlinarith

end NearQuarticWires.StageTuple
