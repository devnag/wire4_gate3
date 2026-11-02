import Proof.Gates.CounterAsm.Copy
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Expand.PolyTab NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

/-- `lem:print`, paper/paper.tex: a source
frame is copied literally, including its own terminal delimiter, into
one further outer frame by a marker-aware physical scan. -/
def doubleFrameProgram : WMX 1 2 :=
  .wm (.seq (NearCubicGates.Close.CounterAsm.frameCopy 0 1 (fun b=>emitPair 1 0 b))
    (emitC 1 0 false))

theorem doubleFrameProgram_run (bits : List Bool) :
    Runs (4*bits.length+4) doubleFrameProgram
      (idealStart 1 2 bits (fun _=>0)) (1000*(bits.length+1))
      (fun z=>z.st 1=frame (frame bits)) := by
  let a:=idealStart 1 2 bits (fun _=>0)
  have hcopy:=NearCubicGates.Close.CounterAsm.frameCopy_spec (cap:=4*bits.length+4)
    (by decide : (0 : Fin 2)≠1) (by decide : (0 : Fin 2)≠1)
    (emits_pair (cap:=4*bits.length+4) (dst:=(1 : Fin 2)) (OP:=(0 : Fin 2)))
    (d:=2) (by intro b;simp) bits [] [] a
    (by simp only [a,idealStart,List.nil_append,List.append_nil];rfl) rfl rfl
    (by simp only [a,idealStart,frame_length];omega)
    (by simp only [a,idealStart,frame_length];omega)
  let b:=adv (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) (1 : Fin 2) a
    ((frame bits).flatMap (fun bit=>[true,bit])) (frame bits).length
  have hb : b.sh 1=(b.st 1).length := by
    simp only [b,adv_sh_dst (by decide : (0 : Fin 2)≠1),adv_st_dst,a,idealStart]
    simp
  have bv : b.val 0+1≤4*bits.length+4 := by
    dsimp only [b]
    rw [adv_val_OP (by decide)]
    simp only [a,idealStart]
    simp
    omega
  have he:=emitC_spec (4*bits.length+4) (1 : Fin 2) (0 : Fin 2) false b hb bv
  refine ⟨appendO b 1 0 [false],?_,?_⟩
  · exact (WXExec.wm (hcopy.seq he)).mono (by rw [frame_length];omega)
  · change (b.st 1++[false])=frame (frame bits)
    rw [show b.st 1=[]++((frame bits).flatMap (fun bit=>[true,bit])) by
      dsimp only [b];rw [adv_st_dst];rfl]
    rw [List.nil_append]
    exact (NearCubicGates.Close.Codec.frame_eq_marks _).symm

/-- `lem:print` and `prop:time`, paper/paper.tex: one ordinary finite-frame scan returns the frame
itself as a framed payload, with linear physical source work. -/
noncomputable def doubleFrameWordFunction {Request : Type} (input : Request→List Bool) :
    WordFunction Request input (fun r=>frame (frame (input r)))
      (fun r=>2000*((input r).length+1)+2) :=
  wordFunction_of_ideal doubleFrameProgram (1 : Fin 2) (by decide)
    (fun r=>4*(input r).length+4) (fun _ _=>0) (fun r=>1000*((input r).length+1))
    (fun _=>by omega) (fun r=>⟨rfl,doubleFrameProgram_run (input r)⟩)

end NearQuarticWires.StageCertNative
