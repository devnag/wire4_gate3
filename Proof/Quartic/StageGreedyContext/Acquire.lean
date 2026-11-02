import Proof.Quartic.StagePacket.ReadLength
import Proof.Gates.Recovery.HTParts

/-!
# Acquisition of only the finite preparation from the framed carrier

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGreedyContext

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print` and `prop:time`, paper/paper.tex: decode only the finite preparation
byte length, copy its marked bytes into the actual context bank,
and leave every count and compiled-entry byte unread. -/
def acquirePrep (src dst : Fin (ns+1)) (R : Fin 16 ↪ Fin nr) : WM ns nr :=
  .seq (readNatM true src (R 6) (R 7) (R 5) (R 8) (R 9))
    (.seq (wcopyR (R 5) (R 10) (R 11))
      (.seq (addTo (R 10) (R 5) (R 11))
        (.seq (cntLoop src (R 2) (R 5) (fun bit=>emitC dst (R 3) bit))
          (.seq (emitC dst (R 3) false) (WM.rewind dst (R 3))))))

/-- `prop:time`, paper/paper.tex: the
preparation acquisition clock is polynomial in its finite byte length
and independent of the numeric walk count and following carrier. -/
def acquirePrepCost (prep : List Bool) : ℕ :=
  (natBitLength prep.length+2)*(40*2^natBitLength prep.length+40)+200*prep.length+100

/-- `lem:print`, paper/paper.tex: the
actual acquisition result keeps the original framed carrier unchanged
and prepares the literal framed source at head zero for one real call. -/
theorem acquirePrep_spec (cap : ℕ) (src dst : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (hsd : src≠dst) (prep suffix pre : List Bool) (a : WState ns nr)
    (hin : a.st src=pre++Streaming.marks (natWord prep.length++prep++suffix)++[false])
    (hhead : a.sh src=pre.length) (hout : a.st dst=[]) (hdhead : a.sh dst=0)
    (hz : ∀j : Fin 16,a.val (R j)=0)
    (hcap : 20*(prep.length+1)+2^(natBitLength prep.length+1)≤cap) :
    ∃b,WExec cap (acquirePrep src dst R) a b (acquirePrepCost prep) ∧
      b.st src=a.st src ∧
      b.sh src=pre.length+2*(natWord prep.length++prep).length ∧
      b.st dst=frame prep ∧ b.sh dst=0 ∧
      b.val (R 2)=2*prep.length ∧ b.val (R 3)=0 ∧ b.val (R 5)=0 ∧
      b.val (R 10)=prep.length ∧
      (∀j : Fin 16,j≠2→j≠10→b.val (R j)=0) ∧
      (∀j,(∀i : Fin 16,R i≠j)→b.val j=a.val j) ∧
      (∀t,t≠src→t≠dst→b.st t=a.st t ∧ b.sh t=a.sh t) := by
  have rn {i j : Fin 16} (h : i≠j) : R i≠R j:=R.injective.ne h
  let header:=Streaming.marks (natWord prep.length)
  let body:=Streaming.marks prep
  have hbits : body.length=2*prep.length:=Streaming.marks_length _
  have hlin : 20*(prep.length+1)≤cap:=(Nat.le_add_right _ _).trans hcap
  have hdec : 2^(natBitLength prep.length+1)≤cap:=(Nat.le_add_left _ _).trans hcap
  have er:=readNatM_spec cap true src (R 6) (R 7) (R 5) (R 8) (R 9)
    (rn (by decide)) (rn (by decide)) (rn (by decide)) (rn (by decide))
    (rn (by decide)) (rn (by decide)) (rn (by decide)) (rn (by decide))
    (rn (by decide)) (rn (by decide)) prep.length pre
    (body++Streaming.marks suffix++[false]) a
    (by simpa only [WireExponent3_5.PrimAsm.ParseNat.enc,if_true,Streaming.marks_append,header,body,List.append_assoc] using hin)
    hhead (hz 6) (hz 7) (hz 8) (hz 9) (by rw [hz 5,Nat.zero_add];exact hdec)
  let b:=(a.seth src (pre.length+2*(natWord prep.length).length)).setv (R 5) prep.length
  have er' : WExec cap (readNatM true src (R 6) (R 7) (R 5) (R 8) (R 9)) a b
      ((natBitLength prep.length+2)*(40*2^natBitLength prep.length+40)) := by
    simpa only [stp,if_true,hz,Nat.zero_add] using er
  have eb:=wcopyR_spec cap (R 5) (R 10) (R 11)
    (rn (by decide)) (rn (by decide)) (rn (by decide)) b
    (by simp [b,R.injective.eq_iff,hz]) (by simp [b,R.injective.eq_iff,hz])
    (by simp [b];omega)
  let c:=b.setv (R 10) prep.length
  have eb' : WExec cap (wcopyR (R 5) (R 10) (R 11)) b c (18*prep.length+3) := by
    simpa only [b,WState.setv_val,Function.update_self] using eb
  have ec:=addTo_spec cap (R 10) (R 5) (R 11)
    (rn (by decide)) (rn (by decide)) (rn (by decide)) c
    (by simp [c,b,R.injective.eq_iff,hz])
    (by simp [c];omega) (by simp [c,b,R.injective.eq_iff];omega)
  let d:=c.setv (R 5) (2*prep.length)
  have ec' : WExec cap (addTo (R 10) (R 5) (R 11)) c d (18*prep.length+3) := by
    simpa only [d,c,b,WState.setv_val,Function.update_self,
      Function.update_of_ne (rn (by decide : (5:Fin 16)≠10)),two_mul] using ec
  have ed:=cntLoop_spec (cap:=cap) (src:=src) (dst:=dst) (OP:=R 3) (SC:=R 2)
    hsd (rn (by decide)) (K:=R 5) (rn (by decide)) (rn (by decide))
    (emits_raw (cap:=cap)) (Streaming.marks suffix++[false]) body (pre++header) d
    (by simp [d,c,b,hin,header,body,Streaming.marks_append,List.append_assoc])
    (by simp [d,c,b,header,Streaming.marks_length])
    (by simp [d,c,b,hsd.symm,hout,hdhead])
    (by simp [d,hbits]) (by omega)
    (by simp [d,c,b,R.injective.eq_iff,hz,hbits];omega)
    (by simp [d,c,b,R.injective.eq_iff,hz,hbits];omega)
  have hbflat : body.flatMap (fun bit=>[bit])=body := by simp
  rw [hbflat] at ed
  let e:=(adv src dst (R 3) (R 2) d body body.length).setv (R 5) 0
  have eeOut : e.sh dst=(e.st dst).length := by
    simp [e,adv,appendO,hsd.symm,d,c,b,hout,hdhead]
  have ee3 : e.val (R 3)=2*prep.length := by
    simp [e,adv,appendO,R.injective.eq_iff,d,c,b,hz,hbits]
  have ee:=NearCubicGates.Close.Codec.emitBit_spec cap dst (R 3) false e eeOut (by rw [ee3];omega)
  let f:=appendO e dst (R 3) [false]
  have ef:=wrewind_spec cap dst (R 3) (2*prep.length+1) f
    (by simp [f,appendO,ee3]) (by simp [f,appendO,ee3];omega)
  let last:=(f.setv (R 3) 0).seth dst (f.sh dst-(2*prep.length+1))
  refine ⟨last,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (er'.seq (eb'.seq (ec'.seq (ed.seq (ee.seq ef))))).mono
      (by unfold acquirePrepCost;rw [hbits];omega)
  · simp [last,f,e,adv,appendO,d,c,b,hsd]
  · simp [last,f,e,adv,appendO,d,c,b,hsd,hbits,List.length_append]
    omega
  · simp [last,f,e,adv,appendO,d,c,b,hout,List.append_assoc]
    exact (NearCubicGates.Close.Codec.frame_eq_marks prep).symm
  · simp [last,f,e,adv,appendO,d,c,b,hout,hdhead,hsd.symm,hbits]
  · simp [last,f,e,adv,appendO,d,c,b,R.injective.eq_iff,hz,hbits]
  · simp [last]
  · simp [last,f,e,R.injective.eq_iff]
  · simp [last,f,e,adv,appendO,d,c,b,R.injective.eq_iff]
  · intro j hj2 hj10
    simp [last,f,e,adv,appendO,d,c,b,Function.update_apply,R.injective.eq_iff,hz,hj2,hj10]
    split_ifs <;> simp_all
  · intro j hj
    simp [last,f,e,adv,appendO,d,c,b,Function.update_of_ne (hj 2).symm,
      Function.update_of_ne (hj 3).symm,Function.update_of_ne (hj 5).symm,
      Function.update_of_ne (hj 10).symm]
  · intro t ht hu
    constructor <;> simp [last,f,e,adv,appendO,d,c,b,Function.update_of_ne ht,Function.update_of_ne hu]

end NearQuarticWires.StageGreedyContext
