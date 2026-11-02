import Proof.Quartic.StagePrintTuple.PayloadCopy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a cache is
erased backwards using its actual scanned-byte counter, returning its
head to zero without sweeping the complete controller capacity. -/
def eraseCacheBackward (src : Fin (ns+1)) (SC : Fin nr) : WM ns nr :=
  .whr SC (.seq (.dec SC) (.seq (.bwd src) (.wr src false)))

/-- `lem:print` and `prop:time`, paper/paper.tex: counted backward erasure overwrites exactly its finite
cache prefix and preserves the remaining tape and all other state. -/
theorem eraseCacheBackward_spec (cap : ℕ) (src : Fin (ns+1)) (SC : Fin nr)
    (bits : List Bool) : ∀ (rest : List Bool) (σ : WState ns nr),
    σ.st src=bits++rest → σ.sh src=bits.length → σ.val SC=bits.length → bits.length≤cap →
    WExec cap (eraseCacheBackward src SC) σ
      (((σ.sets src (List.replicate bits.length false++rest)).seth src 0).setv SC 0)
      (10*bits.length+1) := by
  induction bits using List.reverseRecOn with
  | nil =>
    intro rest σ hs hh hc _hcap
    have he : ((σ.sets src (List.replicate 0 false++rest)).seth src 0).setv SC 0=σ := by
      apply WState.eq
      · funext i;by_cases hi:i=src
        · subst i;simp [hh]
        · simp [Function.update_of_ne hi]
      · simpa using hs.symm
      · funext i;by_cases hi:i=SC
        · subst i;simp [hc]
        · simp [Function.update_of_ne hi]
      · rfl
    have ew : WExec cap (eraseCacheBackward src SC) σ σ 1 := WExec.whrF hc
    exact ew.cast cap he.symm (by simp)
  | append_singleton bits bit ih =>
    intro rest σ hs hh hc hcap
    have hn : σ.val SC≠0 := by simp only [List.length_append,List.length_singleton] at hc;omega
    have e1 := WExec.dec (cap:=cap) SC σ (by rw [hc];exact hcap)
    let a := σ.setv SC (σ.val SC-1)
    have e2 := WExec.bwd (cap:=cap) src a
    let b := a.seth src (a.sh src-1)
    have e3 := WExec.wr (cap:=cap) src false b
    let d := b.sets src (writeTapeBit (b.st src) (b.sh src) false)
    have hwrite : writeTapeBit ((bits++[bit])++rest) bits.length false=bits++false::rest := by
      simp only [List.append_assoc,List.singleton_append]
      exact writeTapeBit_mid bits rest bit false
    have hd : d.st src=bits++false::rest := by
      simp only [d,WState.sets_st,Function.update_self,b,WState.seth_st,a,WState.setv_st,
        WState.seth_sh,Function.update_self,WState.setv_sh,hs,hh,List.length_append,List.length_singleton,
        Nat.add_sub_cancel_right]
      exact hwrite
    have er := ih (false::rest) d hd
      (by simp [d,b,a,hh,List.length_append])
      (by simp [d,b,a,hc,List.length_append]) (by simp only [List.length_append,List.length_singleton] at hcap;omega)
    refine (WExec.whrT hn (e1.seq (e2.seq e3)) er).cast cap ?_ (by simp;omega)
    apply WState.eq
    · funext i
      by_cases hi:i=src
      · subst i;simp
      · simp [d,b,a,Function.update_of_ne hi]
    · funext i
      by_cases hi:i=src
      · subst i
        simp only [WState.setv_st,WState.seth_st,WState.sets_st,Function.update_self,
          List.length_append,List.length_singleton,List.replicate_add,List.replicate_one,
          List.append_assoc,List.singleton_append]
      · simp [d,b,a,Function.update_of_ne hi]
    · funext i
      by_cases hi:i=SC
      · subst i;simp
      · simp [d,b,a,Function.update_of_ne hi]
    · rfl

end NearQuarticWires.StageTuple
