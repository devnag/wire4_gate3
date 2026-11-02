import Proof.Quartic.StageTuplePreparedOutput.MarkedAt
import Proof.Wire_3_5.PrimAsmEmit

set_option autoImplicit false

namespace NearQuarticWires.StageTuplePreparedOutput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the
original raw request has three actual framed source fields before Terms. -/
def prefixBytes (a b c : List Bool) : List Bool := [a,b,c].flatMap frame

/-- `lem:print`, paper/paper.tex: three
actual source frames are scanned without output, and their physically
counted bytes are moved into the retained prefix-rewind counter. -/
def prefixProgram (src : Fin (ns+1)) (SC PRE : Fin nr) : WM ns nr :=
  .seq (NearCubicWires.WireExponent3_5.PrimAsm.Emit.incN PRE 3)
    (.seq (StagePrint.CutScan.skipFields src SC PRE) (WM.move SC PRE))

/-- `lem:print` and `prop:time`, paper/paper.tex: the fixed three-field skip leaves only
the actual source cursor and measured prefix counter, charging every
scan, move and control transition linearly. -/
theorem prefixProgram_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC PRE : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (hPO : PRE≠OP) (hPS : PRE≠SC)
    (a b c rest : List Bool) (σ : WState ns nr)
    (hs : σ.st src=prefixBytes a b c++rest) (hh : σ.sh src=0)
    (hd : σ.sh dst=(σ.st dst).length) (hSC : σ.val SC=0) (hPRE : σ.val PRE=0)
    (hcap : σ.val OP+(prefixBytes a b c).length+4≤cap) :
    WExec cap (prefixProgram src SC PRE) σ
      ((σ.seth src (prefixBytes a b c).length).setv PRE (prefixBytes a b c).length)
      (100*((prefixBytes a b c).length+1)) := by
  have ei := NearCubicWires.WireExponent3_5.PrimAsm.Emit.incN_spec cap PRE 3 σ
    (by rw [hPRE]; omega)
  let u := σ.setv PRE 3
  have ei' : WExec cap (NearCubicWires.WireExponent3_5.PrimAsm.Emit.incN PRE 3) σ u 12 := by
    simpa only [hPRE, Nat.zero_add] using ei
  have es := StagePrint.CutScan.skipFields_spec cap src dst OP SC PRE hsd hOS hPO hPS
    [a,b,c] [] rest u (by simpa [u, prefixBytes] using hs) (by simp [u, hh]) hd
    (by simp [u]) (by simp [u, Function.update_of_ne hPO.symm]; omega)
    (by simp only [u, WState.setv_val, Function.update_of_ne hPS.symm, hSC, Nat.zero_add]
        change (prefixBytes a b c).length≤cap; omega)
    (by simp only [List.length_cons, List.length_nil]; omega)
  let v := (adv src dst OP SC u [] (prefixBytes a b c).length).setv PRE 0
  have vs : v.val SC=(prefixBytes a b c).length := by
    simp [v, adv, u, Function.update_of_ne hPS.symm, hSC]
  have vp : v.val PRE=0 := by simp [v]
  have em := wmove_spec cap SC PRE hPS.symm (prefixBytes a b c).length v vs
    (by rw [vs]; omega) (by rw [vp, vs]; omega)
  refine (ei'.seq (es.seq em)).cast cap ?_ ?_
  · apply WState.eq
    · funext i
      by_cases hi : i=src
      · subst i; simp [v, adv, u, hh]
      · simp [v, adv, u, hi]
    · simp [v, adv, u]
    · funext i
      by_cases hi : i=PRE
      · subst i; simp [vp, vs]
      · by_cases his : i=SC
        · subst i; simp [hPS.symm, hSC]
        · simp [v, adv, u, hi, his]
    · rfl
  · simp only [List.length_cons, List.length_nil]
    change 12+1+(25*(prefixBytes a b c).length+4*3+1+1+
      (7*(prefixBytes a b c).length+1))≤100*((prefixBytes a b c).length+1)
    omega

end NearQuarticWires.StageTuplePreparedOutput
