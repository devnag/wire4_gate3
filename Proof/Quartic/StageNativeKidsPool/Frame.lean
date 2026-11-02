import Proof.Quartic.StageNativeKidsPool.ColdLayout
import Proof.Quartic.StagePrint.ReadFrame
import Proof.Wire_3_5.FinalPassHashTable

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: final
framing uses the actual measured raw-byte counter, retaining implicit
zero data and writing one exact outer frame on a fresh physical tape. -/
def frameProgram (counter row : Program) : WM (streams counter row) 16:=
  let SRC : Fin (streams counter row+1):=⟨14,by unfold streams;omega⟩
  let DST : Fin (streams counter row+1):=⟨15,by unfold streams;omega⟩
  .seq (wcopyR 10 9 0) (.seq (WM.rewind SRC 9)
    (.seq (Codec.frameStream SRC DST 1 10) (emitC DST 1 false)))

/-- `prop:time`, paper/paper.tex: one
complete measured pool frame has a linear physical byte clock. -/
def frameCost (length : ℕ) : ℕ:=100*length+100

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual raw pool, including its final
real delimiter, is framed from measured read bytes without an output
length input, row-count scan or trailing-blank assumption. -/
theorem frame_exec (counter row : Program) (cap : ℕ) (Y : List Bool)
    (σ : WState (streams counter row) 16)
    (hread : ∀k<Y.length,readTapeBit (σ.st ⟨14,by unfold streams;omega⟩) k=Y.getD k false)
    (hsrc : σ.sh ⟨14,by unfold streams;omega⟩=Y.length)
    (hout : σ.st ⟨15,by unfold streams;omega⟩=[]) (houthead : σ.sh ⟨15,by unfold streams;omega⟩=0)
    (hz0 : σ.val (0 : Fin 16)=0) (hz1 : σ.val (1 : Fin 16)=0) (hz9 : σ.val (9 : Fin 16)=0)
    (hlen : σ.val (10 : Fin 16)=Y.length) (hcap : 2*Y.length+1≤cap) :
    Runs cap (.wm (frameProgram counter row)) σ (frameCost Y.length)
      (fun τ=>τ.st ⟨15,by unfold streams;omega⟩=frame Y) := by
  let SRC : Fin (streams counter row+1):=⟨14,by unfold streams;omega⟩
  let DST : Fin (streams counter row+1):=⟨15,by unfold streams;omega⟩
  have hsd : SRC≠DST:=by intro he;have hv:=congrArg Fin.val he;change 14=15 at hv;omega
  have ec:=wcopyR_spec cap (10 : Fin 16) 9 0 (by decide) (by decide) (by decide) σ hz9 hz0 (by omega)
  rw [hlen] at ec
  let s1:=σ.setv 9 Y.length
  have er:=wrewind_spec cap SRC (9 : Fin 16) Y.length s1 rfl
    (by change Y.length≤cap;omega)
  let s2:=(s1.setv 9 0).seth SRC (s1.sh SRC-Y.length)
  have hs2 : s2.sh SRC=0:=by simp [s2,s1,SRC,hsrc]
  have ef:=StagePrint.frameStream_read cap SRC DST hsd (1 : Fin 16) 10 (by decide) Y s2
    (by intro k hk;simpa [s2,s1,SRC,hsrc] using hread k hk)
    (by simp [s2,s1,SRC,DST,hout,houthead])
    (by simp [s2,s1,hlen]) (by omega) (by simp [s2,s1,hz1];omega)
  let s3:=((appendO s2 DST 1 (Streaming.marks Y)).setv 10 0).seth SRC (s2.sh SRC+Y.length)
  have ee:=emitC_spec cap DST (1 : Fin 16) false s3
    (by simp [s3,appendO,s2,s1,SRC,DST,hout,houthead,Streaming.marks_length])
    (by simp [s3,appendO,s2,s1,hz1,Streaming.marks_length];omega)
  refine (Runs.of (WXExec.wm (ec.seq (er.seq (ef.seq ee)))) ?_).cost ?_
  · simp [appendO,s3,s2,s1,SRC,DST,hout,Codec.frame_eq_marks]
  · unfold frameCost
    omega

end NearQuarticWires.StageNativeKidsPool
