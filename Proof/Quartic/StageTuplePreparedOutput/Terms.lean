import Proof.Quartic.StageTuplePreparedOutput.Prefix

set_option autoImplicit false

namespace NearQuarticWires.StageTuplePreparedOutput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: exactly
the fourth original frame is copied, following three actual frame
scans and before a rewind by the physically measured source prefix. -/
def termsProgram (src dst : Fin (ns+1)) (OP SC PRE : Fin nr) : WM ns nr :=
  .seq (prefixProgram src SC PRE)
    (.seq (appendMarkedFrameReset src dst OP SC) (WM.rewind src PRE))

/-- `lem:print` and `prop:time`, paper/paper.tex: the whole original Terms field is
copied once without parsing it, all actual source and scratch state is
restored, and the complete source scan is charged only linearly. -/
theorem termsProgram_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC PRE : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (hPO : PRE≠OP) (hPS : PRE≠SC)
    (a b c terms rest : List Bool) (σ : WState ns nr)
    (hs : σ.st src=prefixBytes a b c++frame terms++rest) (hh : σ.sh src=0)
    (hd : σ.sh dst=(σ.st dst).length) (hSC : σ.val SC=0) (hPRE : σ.val PRE=0)
    (hcap : σ.val OP+(prefixBytes a b c).length+2*(frame terms).length+10≤cap) :
    WExec cap (termsProgram src dst OP SC PRE) σ
      (appendO σ dst OP (marks (frame terms)))
      (500*((prefixBytes a b c).length+(frame terms).length+1)) := by
  have ep := prefixProgram_spec cap src dst OP SC PRE hsd hOS hPO hPS a b c
    (frame terms++rest) σ (by simpa only [List.append_assoc] using hs) hh hd hSC hPRE (by omega)
  let u := (σ.seth src (prefixBytes a b c).length).setv PRE (prefixBytes a b c).length
  have uop : u.val OP=σ.val OP := by simp [u, hPO.symm]
  have ec := appendMarkedFrameAtReset_spec cap src dst OP SC hsd hOS terms (prefixBytes a b c) rest u
    (by simp [u, hs]) (by simp [u])
    (by simpa [u, Function.update_of_ne hsd.symm] using hd)
    (by simpa [u, Function.update_of_ne hPS.symm] using hSC)
    (by rw [uop]; omega)
  let v := appendO u dst OP (marks (frame terms))
  have vp : v.val PRE=(prefixBytes a b c).length := by simp [v, appendO, u, hPO]
  have er := wrewind_spec cap src PRE (prefixBytes a b c).length v vp (by rw [vp]; omega)
  refine (ep.seq (ec.seq er)).cast cap ?_ ?_
  · apply WState.eq
    · funext i
      by_cases hi : i=src
      · subst i; simp [v, u, appendO, hsd, hh]
      · by_cases hid : i=dst
        · subst i; simp [v, u, appendO, hsd.symm]
        · simp [v, u, appendO, hi, hid]
    · rfl
    · funext i
      by_cases hi : i=PRE
      · subst i; simp [appendO, hPO, hPRE]
      · by_cases hio : i=OP
        · subst i; simp [v, u, appendO, hPO.symm]
        · simp [v, u, appendO, hi, hio]
    · rfl
  · unfold appendMarkedFrameCost
    omega

end NearQuarticWires.StageTuplePreparedOutput
