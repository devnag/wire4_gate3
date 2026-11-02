import Proof.Quartic.StagePacket.ReadLength
import Proof.Quartic.StagePacket.ProjectionCodec

set_option autoImplicit false

namespace NearQuarticWires.StagePacket

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts
open StagePrint.PacketInterface NearCubicGates.Close.Interfaces.Formats

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the encoded
index is retained; the remaining indexed fields are physically
consumed, decoding only the actual payload byte count. -/
def projectPrefix (src idx : Fin (ns+1)) (R : Fin 16 ↪ Fin nr) : WM ns nr :=
  .seq (natCopy src (R 2) (R 4) (fun bit=>emitPair idx (R 3) bit))
    (.seq (emitC idx (R 3) false)
      (.seq (copyNaturalFields src (R 2) (R 4) (fun _=>.skip) 2)
        (.seq (readPayloadLength src R)
          (copyNaturalFields src (R 2) (R 4) (fun _=>.skip) 2))))

/-- `lem:print`, paper/paper.tex: the first
actual copy retains the index's encoded bits without unary decoding. -/
def projectionIndexState (src idx : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (a : WState ns nr) (r : ExactProjectionRequest) : WState ns nr :=
  appendO (adv src idx (R 3) (R 2) a ((natWord r.index).flatMap fun bit=>[true,bit])
    (natWord r.index).length) idx (R 3) [false]

/-- `lem:print`, paper/paper.tex: the two
public hints before the byte-count field are skipped by their codecs. -/
def projectionLeftState (src idx : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (a : WState ns nr) (r : ExactProjectionRequest) : WState ns nr :=
  adv src idx (R 3) (R 2) (projectionIndexState src idx R a r) []
    ([r.setupHint,r.degree].flatMap natWord).length

/-- `lem:print`, paper/paper.tex: measured
length is increased by the physically decoded fourth codec. -/
def projectionLengthState (src idx : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (a : WState ns nr) (r : ExactProjectionRequest) (position : ℕ) : WState ns nr :=
  payloadLengthState src R (projectionLeftState src idx R a r)
    (position+(natWord r.index).length+([r.setupHint,r.degree].flatMap natWord).length) r.payload.length

/-- `lem:print`, paper/paper.tex: the final
two indexed fields are skipped with the same actual measured reader. -/
def projectionPrefixState (src idx : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (a : WState ns nr) (r : ExactProjectionRequest) (position : ℕ) : WState ns nr :=
  adv src idx (R 3) (R 2) (projectionLengthState src idx R a r position) []
    ([r.hint,0].flatMap natWord).length

/-- `prop:time`, paper/paper.tex: the prefix
clock charges the actual codecs and actual payload-count decoder. -/
def projectionPrefixCost (r : ExactProjectionRequest) : ℕ :=
  28*(natWord r.index).length+11+
    (13*([r.setupHint,r.degree].flatMap natWord).length+2)+
    payloadLengthCost r.payload.length+(13*([r.hint,0].flatMap natWord).length+2)

/-- `lem:print`, paper/paper.tex: every prefix
copy preserves registers outside its two actual measured counters. -/
theorem projectionLeftState_val (src idx : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (a : WState ns nr) (r : ExactProjectionRequest) (j : Fin 16) (h2 : j≠2) (h3 : j≠3) :
    (projectionLeftState src idx R a r).val (R j)=a.val (R j) := by
  simp only [projectionLeftState,projectionIndexState,
    adv_val_other _ _ _ _ (register_ne R h3) (register_ne R h2),
    appendO_val,Function.update_of_ne (register_ne R h3)]

/-- `lem:print` and `prop:time`, paper/paper.tex: the real six-field prefix reader stops at Formula's
first byte, with a paid encoded index and a measured source cursor. -/
theorem projectPrefix_spec (cap : ℕ) (src idx : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (hsi : src≠idx) (r : ExactProjectionRequest) (pre suffix : List Bool) (a : WState ns nr)
    (hsource : a.st src=pre++r.word++suffix) (hhead : a.sh src=pre.length)
    (hi : a.st idx=[]) (hih : a.sh idx=0)
    (hzero : ∀ j : Fin 16,j≠1→a.val (R j)=0)
    (hcap : pre.length+4*r.word.length+20≤cap) :
    WExec cap (projectPrefix src idx R) a (projectionPrefixState src idx R a r pre.length)
      (projectionPrefixCost r) := by
  have h32 : R 3≠R 2 := register_ne R (by decide)
  have h43 : R 4≠R 3 := register_ne R (by decide)
  have h42 : R 4≠R 2 := register_ne R (by decide)
  let ib:=natWord r.index
  let left:=[r.setupHint,r.degree].flatMap natWord
  let right:=[r.hint,0].flatMap natWord
  let lb:=natWord r.payload.length
  have hword : r.word=ib++left++lb++right++formulaWord r.formula := by
    simp only [ExactProjectionRequest.word,ib,left,right,lb,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.append_assoc]
  have hm : r.word.length=ib.length+left.length+lb.length+right.length+(formulaWord r.formula).length := by
    rw [hword]
    simp only [List.length_append]
  have hpayload : r.payload.length≤(formulaWord r.formula).length := by
    rw [projection_formula_word,List.length_append]
    omega
  have eIndex:=natCopy_spec cap hsi h32 h43 h42 (emits_pair (cap:=cap)) (d:=2) (by intro bit;simp)
    r.index pre (left++lb++right++formulaWord r.formula++suffix) a
    (by simpa only [hword,List.append_assoc] using hsource) hhead (by rw [hi,hih];rfl)
    (hzero 4 (by decide)) (by rw [hzero 3 (by decide)];dsimp only [ib] at hm;omega)
    (by rw [hzero 2 (by decide)];dsimp only [ib] at hm;omega)
    (by dsimp only [ib] at hm;omega)
  let b:=adv src idx (R 3) (R 2) a (ib.flatMap fun bit=>[true,bit]) ib.length
  have hbout : b.sh idx=(b.st idx).length := by
    rw [adv_sh_dst hsi,adv_st_dst,hi,hih]
    simp
  have eMark:=NearCubicGates.Close.Codec.emitBit_spec cap idx (R 3) false b hbout (by
    rw [adv_val_OP h32,hzero 3 (by decide),paired_length]
    omega)
  let c:=projectionIndexState src idx R a r
  have hcK : c.val (R 4)=0 := by
    simp [c,projectionIndexState,adv,appendO,Function.update_apply,R.injective.eq_iff,hzero]
  have hc2 : c.val (R 2)=ib.length := by
    simp [c,projectionIndexState,adv,appendO,Function.update_apply,R.injective.eq_iff,hzero,ib]
  have hc3 : c.val (R 3)=2*ib.length+1 := by
    simp [c,projectionIndexState,adv,appendO,Function.update_apply,R.injective.eq_iff,hzero,
      ib,Nat.mul_comm]
  have eLeft:=copyNaturalFields_spec cap src idx (R 3) (R 2) (R 4) hsi
    h32 h43 h42
    (fun _=>.skip) (fun _=>[]) 0 0 (emits_none (cap:=cap)) (by intro bit;rfl)
    [r.setupHint,r.degree] (pre++ib) (lb++right++formulaWord r.formula++suffix) c
    (by simp only [c,projectionIndexState,appendO_st,Function.update_of_ne hsi,adv_st_src hsi,
      hsource,hword,List.append_assoc];rfl)
    (by simp only [c,projectionIndexState,appendO_sh,Function.update_of_ne hsi,
      adv_sh_src,hhead,List.length_append];rfl)
    (by simp only [c,projectionIndexState,appendO_sh,appendO_st,Function.update_self,
      adv_sh_dst hsi,adv_st_dst,hi,hih,List.nil_append,Nat.zero_add,List.length_append])
    hcK (by rw [hc3];simp only [Nat.zero_mul,Nat.add_zero];omega)
    (by rw [hc2];change ib.length+left.length≤cap;omega)
  have eLeft' : WExec cap (copyNaturalFields src (R 2) (R 4) (fun _=>.skip) 2) c
      (projectionLeftState src idx R a r) (13*left.length+2) := by
    simpa [projectionLeftState,c,left,Nat.mul_comm,projection_empty_map] using eLeft
  let d:=projectionLeftState src idx R a r
  have hd2 : d.val (R 2)=ib.length+left.length := by
    dsimp only [d,projectionLeftState]
    rw [adv_val_SC]
    exact congrArg (fun value=>value+left.length) hc2
  have hd3 : d.val (R 3)=2*ib.length+1 := by
    change (adv src idx (R 3) (R 2) c [] left.length).val (R 3)=_
    rw [adv_val_OP h32,hc3,List.length_nil,Nat.add_zero]
  have hdsource : d.st src=(pre++ib++left)++natWord r.payload.length++
      (right++formulaWord r.formula++suffix) := by
    simp only [d,projectionLeftState,adv_st_src hsi,projectionIndexState,
      appendO_st,Function.update_of_ne hsi,hsource,hword,List.append_assoc]
    rfl
  have hdhead : d.sh src=(pre++ib++left).length := by
    simp only [d,projectionLeftState,adv_sh_src,projectionIndexState,
      appendO_sh,Function.update_of_ne hsi,hhead,List.length_append]
    rfl
  have eLength:=readPayloadLength_spec cap src R r.payload.length (pre++ib++left)
    (right++formulaWord r.formula++suffix) d hdsource hdhead
    (by
      intro j hj
      have hj2 : j≠2 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;omega
      have hj3 : j≠3 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;omega
      rw [projectionLeftState_val src idx R a r j hj2 hj3]
      exact hzero j (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;omega))
    (by have hp:=projection_power_bound r.payload.length;rw [pow_succ];omega)
    (by omega) (by rw [hd2];change ib.length+left.length+lb.length≤cap;omega)
  let e:=projectionLengthState src idx R a r pre.length
  have he2 : e.val (R 2)=ib.length+left.length+lb.length := by
    simp only [e,projectionLengthState,payloadLengthState,WState.setv_val,Function.update_self]
    exact congrArg (fun value=>value+lb.length) hd2
  have he3 : e.val (R 3)=2*ib.length+1 := by
    simpa [e,projectionLengthState,payloadLengthState,Function.update_apply,R.injective.eq_iff] using hd3
  have heK : e.val (R 4)=0 := by
    have hdK:=projectionLeftState_val src idx R a r 4 (by decide) (by decide)
    simpa [e,projectionLengthState,payloadLengthState,Function.update_apply,R.injective.eq_iff,
      hzero] using hdK
  have eRight:=copyNaturalFields_spec cap src idx (R 3) (R 2) (R 4) hsi
    h32 h43 h42
    (fun _=>.skip) (fun _=>[]) 0 0 (emits_none (cap:=cap)) (by intro bit;rfl)
    [r.hint,0] (pre++ib++left++lb) (formulaWord r.formula++suffix) e
    (by simp only [e,projectionLengthState,payloadLengthState,WState.setv_st,WState.seth_st,
      projectionLeftState,projectionIndexState,appendO_st,
      Function.update_of_ne hsi,adv_st_src hsi,hsource,hword,List.append_assoc];rfl)
    (by simp only [e,projectionLengthState,payloadLengthState,WState.setv_sh,WState.seth_sh,
      Function.update_self,List.length_append];rfl)
    (by simp only [e,projectionLengthState,payloadLengthState,WState.setv_sh,WState.setv_st,
      WState.seth_sh,WState.seth_st,Function.update_of_ne hsi.symm,projectionLeftState,
      adv_sh_dst hsi,adv_st_dst,projectionIndexState,appendO_sh,appendO_st,
      Function.update_self,hi,hih,List.nil_append,
      List.length_append,List.length_nil,Nat.add_zero,Nat.zero_add])
    heK (by rw [he3];simp only [Nat.zero_mul,Nat.add_zero];omega)
    (by rw [he2];change ib.length+left.length+lb.length+right.length≤cap;omega)
  have eRight' : WExec cap (copyNaturalFields src (R 2) (R 4) (fun _=>.skip) 2) e
      (projectionPrefixState src idx R a r pre.length) (13*right.length+2) := by
    simpa [projectionPrefixState,e,right,Nat.mul_comm,projection_empty_map] using eRight
  have hLengthState : payloadLengthState src R d (pre++ib++left).length r.payload.length=e := by
    simp only [e,projectionLengthState,List.length_append]
    rfl
  rw [hLengthState] at eLength
  refine WExec.cast cap (WExec.seq eIndex (WExec.seq eMark
    (WExec.seq eLeft' (WExec.seq eLength eRight')))) rfl ?_
  dsimp only [projectionPrefixCost,ib,left,right]
  omega

end NearQuarticWires.StagePacket
