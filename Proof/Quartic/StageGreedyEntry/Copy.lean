import Proof.Gates.CounterAsm.Copy

/-!
# Frame scans for the per-entry reformatters

Paper: `lem:print` and `prop:time`, paper/paper.tex.

`framesCopy` passes a fixed number of consecutive frames through an emitter (`framesCopy_spec`);
`unframeP` decodes one frame onto a stream (`unframe_spec`); `unaryFrameP` appends the marked image
of a unary frame `frame (1^v)` from a counter (`unaryFrame_spec`). Every step is linear in the bits it
reads or writes and never decodes a binary magnitude.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ} (cap : ℕ)

/-- `lem:print`, paper/paper.tex: `k` consecutive frames through one emitter. -/
def framesCopy (src : Fin (ns+1)) (SC : Fin nr) (E : Bool→WM ns nr) : ℕ→WM ns nr
  | 0=>.skip
  | k+1=>.seq (frameCopy src SC E) (framesCopy src SC E k)

theorem framesCopy_spec {src dst : Fin (ns+1)} {OP SC : Fin nr} (hsd : src≠dst) (hOS : OP≠SC)
    {e : Bool→List Bool} {E : Bool→WM ns nr} {c d : ℕ} (hE : Emits cap dst OP e E c) (hd' : EmitLen e d) :
    ∀ (xs : List (List Bool)) (pre rest : List Bool) (σ : WState ns nr),
      σ.st src=pre++xs.flatMap frame++rest → σ.sh src=pre.length → σ.sh dst=(σ.st dst).length →
      σ.val OP+d*(xs.flatMap frame).length≤cap → σ.val SC+(xs.flatMap frame).length<cap+1 →
      WExec cap (framesCopy src SC E xs.length) σ
        (adv src dst OP SC σ ((xs.flatMap frame).flatMap e) (xs.flatMap frame).length)
        ((xs.flatMap frame).length*(2*c+26))
  | [],pre,rest,σ,_,_,_,_,_=>by
    simp only [List.flatMap_nil,List.length_nil,adv_zero,Nat.zero_mul]
    exact WExec.skip σ
  | x::xs,pre,rest,σ,hst,hsh,hd,hOc,hSc=>by
    have hL : ((x::xs).flatMap frame).length=(frame x).length+(xs.flatMap frame).length := by simp
    rw [hL] at hOc hSc
    have x1:=frameCopy_spec cap hsd hOS hE hd' x pre (xs.flatMap frame++rest) σ
      (by rw [hst];simp [List.append_assoc]) hsh hd (by nlinarith) (by omega)
    set σ1:=adv src dst OP SC σ ((frame x).flatMap e) (frame x).length with hσ1
    have hfe:=flatMap_emit_le hd' (frame x)
    have ih:=framesCopy_spec hsd hOS hE hd' xs (pre++frame x) rest σ1
      (by rw [hσ1,adv_st_src hsd,hst];simp [List.append_assoc])
      (by rw [hσ1,adv_sh_src,hsh];simp)
      (by rw [hσ1,adv_sh_dst hsd,adv_st_dst];simp [hd])
      (by rw [hσ1,adv_val_OP hOS];nlinarith)
      (by rw [hσ1,adv_val_SC];omega)
    have hx1 : 1≤(frame x).length := by rw [frame_length];omega
    refine WExec.mono (WExec.cast cap (WExec.seq x1 ih) ?_ le_rfl) (by rw [hL];nlinarith)
    rw [hσ1,adv_adv hsd hOS]
    simp [List.flatMap_append]

theorem flatMap_raw : ∀ w : List Bool,(w.flatMap fun b=>([] : List Bool)++[b])=w
  | []=>rfl
  | b::w=>by
    have h:=flatMap_raw w
    simp only [List.flatMap_cons,List.nil_append] at h ⊢
    rw [h];rfl

/-- `lem:print`, paper/paper.tex: decode one frame onto `dst`. -/
def unframeP (src dst : Fin (ns+1)) (SC OP : Fin nr) : WM ns nr :=
  .seq (pairLoop src SC (fun _=>.skip) (fun b=>emitC dst OP b)) (cellE src SC (fun _=>.skip))

theorem unframe_spec {src dst : Fin (ns+1)} {OP SC : Fin nr} (hsd : src≠dst) (hOS : OP≠SC)
    (w pre rest : List Bool) (σ : WState ns nr) (hst : σ.st src=pre++frame w++rest)
    (hsh : σ.sh src=pre.length) (hd : σ.sh dst=(σ.st dst).length)
    (hOc : σ.val OP+w.length≤cap) (hSc : σ.val SC+2*w.length+1<cap+1) :
    WExec cap (unframeP src dst SC OP) σ (adv src dst OP SC σ w (2*w.length+1)) (24*w.length+9) := by
  have hE1 : Emits cap dst OP (fun _=>[]) (fun _=>WM.skip) 0 := emits_none cap
  have hE2 : Emits cap dst OP (fun b=>[b]) (fun b=>emitC dst OP b) 7 := emits_raw cap
  have hw : (w.flatMap fun b=>([] : List Bool)++[b])=w := flatMap_raw w
  have x1:=pairLoop_spec cap hsd hOS hE1 hE2 (false::rest) (by simp) w pre σ
    (by rw [hst,NearCubicGates.Close.Codec.frame_eq_marks];simp [List.append_assoc]) hsh hd
    (by rw [hw];exact hOc) (by omega)
  rw [hw] at x1
  set σ1:=adv src dst OP SC σ w (2*w.length) with hσ1
  have hb : readTapeBit (σ1.st src) (σ1.sh src)=false := by
    rw [hσ1,adv_st_src hsd,adv_sh_src,hst,hsh,NearCubicGates.Close.Codec.frame_eq_marks]
    simp only [List.append_assoc]
    rw [NearCubicGates.Close.CheckedPCPP.LitDecode.rtb_off pre _ (2*w.length)]
    unfold readTapeBit
    simp
  have x2:=cellE_spec cap hsd hOS hE1 σ1 (by rw [hσ1,adv_sh_dst hsd,adv_st_dst];simp [hd])
    (by rw [hσ1,adv_val_OP hOS];simp;omega) (by rw [hσ1,adv_val_SC];omega)
  refine WExec.mono (WExec.cast cap (WExec.seq x1 x2) ?_ le_rfl) (by omega)
  rw [hσ1,adv_adv hsd hOS]
  simp

/-- `lem:print`, paper/paper.tex: the marked body of one frame, without its end marker. -/
def markCopyP (src dst : Fin (ns+1)) (SC OP : Fin nr) : WM ns nr :=
  .seq (pairLoop src SC (fun b=>emitC dst OP b) (fun b=>emitC dst OP b)) (cellE src SC (fun _=>.skip))

theorem flatMap_marks : ∀ w : List Bool,(w.flatMap fun b=>[true]++[b])=marks w
  | []=>rfl
  | b::w=>by
    have h:=flatMap_marks w
    simp only [List.flatMap_cons] at h ⊢
    rw [h];rfl

theorem markCopy_spec {src dst : Fin (ns+1)} {OP SC : Fin nr} (hsd : src≠dst) (hOS : OP≠SC)
    (w pre rest : List Bool) (σ : WState ns nr) (hst : σ.st src=pre++frame w++rest)
    (hsh : σ.sh src=pre.length) (hd : σ.sh dst=(σ.st dst).length)
    (hOc : σ.val OP+2*w.length≤cap) (hSc : σ.val SC+2*w.length+1<cap+1) :
    WExec cap (markCopyP src dst SC OP) σ (adv src dst OP SC σ (marks w) (2*w.length+1)) (31*w.length+9) := by
  have hE : Emits cap dst OP (fun b=>[b]) (fun b=>emitC dst OP b) 7 := emits_raw cap
  have hE1 : Emits cap dst OP (fun _=>[]) (fun _=>WM.skip) 0 := emits_none cap
  have x1:=pairLoop_spec cap hsd hOS hE hE (false::rest) (by simp) w pre σ
    (by rw [hst,NearCubicGates.Close.Codec.frame_eq_marks];simp [List.append_assoc]) hsh hd
    (by rw [flatMap_marks,NearCubicWires.RepairOrdinary.Streaming.marks_length];exact hOc) (by omega)
  rw [flatMap_marks] at x1
  set σ1:=adv src dst OP SC σ (marks w) (2*w.length) with hσ1
  have hb : readTapeBit (σ1.st src) (σ1.sh src)=false := by
    rw [hσ1,adv_st_src hsd,adv_sh_src,hst,hsh,NearCubicGates.Close.Codec.frame_eq_marks]
    simp only [List.append_assoc]
    rw [NearCubicGates.Close.CheckedPCPP.LitDecode.rtb_off pre _ (2*w.length)]
    unfold readTapeBit
    simp
  have x2:=cellE_spec cap hsd hOS hE1 σ1 (by rw [hσ1,adv_sh_dst hsd,adv_st_dst];simp [hd])
    (by rw [hσ1,adv_val_OP hOS];simp;omega) (by rw [hσ1,adv_val_SC];omega)
  refine WExec.mono (WExec.cast cap (WExec.seq x1 x2) ?_ le_rfl) (by omega)
  rw [hσ1,adv_adv hsd hOS]
  simp

end NearQuarticWires.StageGreedyEntry
