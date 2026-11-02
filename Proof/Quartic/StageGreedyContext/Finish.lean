import Proof.Quartic.StageGreedyContext.Acquire
import Proof.Gates.Codec.Unframe

/-!
# One final linear copy of the unchanged carrier suffix

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGreedyContext

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.Codec NearCubicGates.Close.CounterAsm
open NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: reframe
the one finite common context and copy the original count and all
entry bytes directly from their untouched outer-marked source. -/
def finishContext (src cache dst : Fin (ns+1)) (CP OP SC : Fin nr) : WM ns nr :=
  .seq (WM.rewind cache CP)
    (.seq (frameCopy cache SC (fun bit=>emitPair dst OP bit))
      (.seq (.whs src (copyPairW src dst OP)) (emitC dst OP false)))

/-- `prop:time`, paper/paper.tex: the
actual final stream work is linear in the context and unchanged
suffix bytes, independently of every numeric entry index and count. -/
def finishContextCost (context suffix : List Bool) : ℕ :=
  200*(context.length+suffix.length+1)

/-- `lem:print` and `prop:time`, paper/paper.tex: the final physical pass emits exactly
one outer frame containing the inner context frame and every
unchanged suffix bit, copying each original suffix byte once. -/
theorem finishContext_spec (cap : ℕ) (src cache dst : Fin (ns+1))
    (CP OP SC : Fin nr) (hsc : src≠cache) (hsd : src≠dst) (hcd : cache≠dst)
    (hregs : ([CP,OP,SC] : List (Fin nr)).Nodup)
    (context suffix pre : List Bool) (a : WState ns nr)
    (hin : a.st src=pre++frame suffix) (hhead : a.sh src=pre.length)
    (hcache : a.st cache=frame context) (hcHead : a.sh cache=(frame context).length)
    (hout : a.st dst=[]) (hoHead : a.sh dst=0)
    (hCP : a.val CP=(frame context).length) (hOP : a.val OP=0) (hSC : a.val SC=0)
    (hcap : 100*(context.length+suffix.length+1)≤cap) :
    ∃b,WExec cap (finishContext src cache dst CP OP SC) a b (finishContextCost context suffix) ∧
      b.st dst=frame (frame context++suffix) := by
  have hCO : CP≠OP:=by
    intro h;exact (List.nodup_cons.mp hregs).1 (by simp [h])
  have hCS : CP≠SC:=by
    intro h;exact (List.nodup_cons.mp hregs).1 (by simp [h])
  have hOS : OP≠SC:=by simpa using (List.nodup_cons.mp (List.nodup_cons.mp hregs).2).1
  have hlen : (frame context).length=2*context.length+1:=by
    rw [frame_eq_marks]
    simp only [List.length_append,Streaming.marks_length,List.length_singleton]
  have er:=wrewind_spec cap cache CP (frame context).length a hCP (by rw [hCP,hlen];omega)
  let a1:=(a.setv CP 0).seth cache 0
  have er' : WExec cap (WM.rewind cache CP) a a1 (5*(frame context).length+1) := by
    simpa only [a1,hcHead,Nat.sub_self] using er
  have eframe:=frameCopy_spec (cap:=cap) (d:=2) hcd hOS (emits_pair (cap:=cap))
    (by intro bit;exact le_rfl) context [] [] a1
    (by simpa [a1] using hcache) (by simp [a1])
    (by simp [a1,hcd.symm,hout,hoHead])
    (by simp [a1,hCO.symm,hOP,hlen];omega)
    (by simp [a1,hCS.symm,hSC,hlen];omega)
  let b:=adv cache dst OP SC a1 (Streaming.marks (frame context)) (frame context).length
  have eframe' : WExec cap (frameCopy cache SC (fun bit=>emitPair dst OP bit)) a1 b
      (55*(frame context).length) := by
    simpa only [b,Streaming.marks,Nat.reduceMul,Nat.reduceAdd,Nat.mul_comm] using eframe
  have bSource : b.st src=pre++frame suffix := by
    simp [b,adv,appendO,a1,Function.update_of_ne hsd,hin]
  have bHead : b.sh src=pre.length := by
    simp [b,adv,appendO,a1,Function.update_of_ne hsc,Function.update_of_ne hsd,hhead]
  have bOut : b.st dst=Streaming.marks (frame context) := by simp [b,adv,appendO,a1,hout]
  have bOutHead : b.sh dst=(b.st dst).length := by
    simp [b,adv,appendO,a1,hcd.symm,hout,hoHead]
  have bOP : b.val OP=2*(frame context).length := by
    simp [b,adv,appendO,a1,hCO.symm,hOS,hOP,Streaming.marks_length]
  have esuffix:=copyFrame_loop cap src dst hsd OP [] suffix pre b
    (by simpa using bSource) bHead bOutHead (by rw [bOP,hlen];omega)
  let c:=(appendO b dst OP (Streaming.marks suffix)).seth src (pre.length+2*suffix.length)
  have cOut : c.st dst=Streaming.marks (frame context)++Streaming.marks suffix := by
    simp [c,appendO,bOut]
  have cOutHead : c.sh dst=(c.st dst).length := by
    simp [c,appendO,hsd.symm,bOutHead]
  have ec:=emitC_spec cap dst OP false c cOutHead
    (by simp [c,appendO,bOP,Streaming.marks_length,hlen];omega)
  refine ⟨appendO c dst OP [false],(er'.seq (eframe'.seq (esuffix.seq ec))).mono ?_,?_⟩
  · unfold finishContextCost
    rw [hlen]
    omega
  · simp only [appendO_st,Function.update_self,cOut,frame_eq_marks,Streaming.marks_append,
      List.append_assoc]

end NearQuarticWires.StageGreedyContext
