import Proof.Quartic.StageGreedyContext.Acquire

/-!
# A marked finite field is decoded with an exactly measured head return

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGreedyContext

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

variable {ns nr : ℕ}

/-- `prop:time`, paper/paper.tex: four
actual scalar additions measure the marked natural-field prefix. -/
def addFour (value counter scratch : Fin nr) : WM ns nr :=
  .seq (addTo value counter scratch) (.seq (addTo value counter scratch)
    (.seq (addTo value counter scratch) (addTo value counter scratch)))

/-- `prop:time`, paper/paper.tex: the
measured prefix counter is computed by physical instructions, with
its real addition cost and no supplied offset. -/
theorem addFour_spec (cap : ℕ) (value counter scratch : Fin nr)
    (hvc : value≠counter) (hvs : value≠scratch) (hcs : counter≠scratch)
    (a : WState ns nr) (n : ℕ) (hv : a.val value=n) (hz : a.val scratch=0)
    (hcap : a.val counter+4*n≤cap) :
    WExec cap (addFour value counter scratch) a
      (a.setv counter (a.val counter+4*n)) (72*n+15) := by
  have hn : n≤cap:=by omega
  have e1:=addTo_spec cap value counter scratch hvc hvs hcs a hz (by rw [hv];exact hn)
    (by rw [hv];omega)
  rw [hv] at e1
  let b:=a.setv counter (a.val counter+n)
  have bv : b.val value=n:=by simp [b,hvc,hv]
  have bs : b.val scratch=0:=by simp [b,hcs.symm,hz]
  have e2:=addTo_spec cap value counter scratch hvc hvs hcs b bs (by rw [bv];exact hn)
    (by simp [b,bv];omega)
  rw [bv,show b.val counter=a.val counter+n by simp [b]] at e2
  let c:=b.setv counter (a.val counter+2*n)
  have e2' : WExec cap (addTo value counter scratch) b c (18*n+3) := by
    convert e2 using 1
    dsimp only [c]
    congr 1
    omega
  have cv : c.val value=n:=by simp [c,hvc,bv]
  have cs : c.val scratch=0:=by simp [c,hcs.symm,bs]
  have e3:=addTo_spec cap value counter scratch hvc hvs hcs c cs (by rw [cv];exact hn)
    (by simp [c,cv];omega)
  rw [cv,show c.val counter=a.val counter+2*n by simp [c]] at e3
  let d:=c.setv counter (a.val counter+3*n)
  have e3' : WExec cap (addTo value counter scratch) c d (18*n+3) := by
    convert e3 using 1
    dsimp only [d]
    congr 1
    omega
  have dv : d.val value=n:=by simp [d,hvc,cv]
  have ds : d.val scratch=0:=by simp [d,hcs.symm,cs]
  have e4:=addTo_spec cap value counter scratch hvc hvs hcs d ds (by rw [dv];exact hn)
    (by simp [d,dv];omega)
  rw [dv,show d.val counter=a.val counter+3*n by simp [d]] at e4
  refine WExec.cast cap (e1.seq (e2'.seq (e3'.seq e4))) ?_ ?_
  · simp only [d,c,b,wsetv_setv]
    congr 1
    omega
  · omega

/-- `lem:print` and `prop:time`, paper/paper.tex: decode one marked natural field,
compute its actual binary length, and return its source head exactly. -/
def readFieldRestore (src : Fin (ns+1)) (R : Fin 16 ↪ Fin nr) : WM ns nr :=
  .seq (readNatM true src (R 6) (R 7) (R 5) (R 8) (R 9))
    (.seq (bitLenM (StagePacket.lengthRegisters R))
      (.seq (addFour (R 10) (R 2) (R 11))
        (.seq (.inc (R 2)) (.seq (.inc (R 2))
          (.seq (WM.rewind src (R 2)) (WM.clear (R 10)))))))

/-- `prop:time`, paper/paper.tex: the
marked-field reader pays the actual finite decoder, bit-length work,
counter additions and measured head return. -/
def readFieldCost (n : ℕ) : ℕ :=
  (natBitLength n+2)*(40*2^natBitLength n+40)+60*n+300*natBitLength n+200

/-- `lem:print`, paper/paper.tex: the
physical field reader preserves its whole source, restores the actual
initial head, and retains only the decoded finite scalar. -/
theorem readFieldRestore_spec (cap : ℕ) (src : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (n : ℕ) (pre rest : List Bool) (a : WState ns nr)
    (hin : a.st src=pre++Streaming.marks (natWord n)++rest)
    (hhead : a.sh src=pre.length) (hz : ∀j : Fin 16,a.val (R j)=0)
    (hcap : 20*(n+natBitLength n+1)+2^(natBitLength n+1)≤cap) :
    WExec cap (readFieldRestore src R) a (a.setv (R 5) n) (readFieldCost n) := by
  have rn {i j : Fin 16} (h : i≠j) : R i≠R j:=R.injective.ne h
  have hl : 20*(n+natBitLength n+1)≤cap:=(Nat.le_add_right _ _).trans hcap
  have hd : 2^(natBitLength n+1)≤cap:=(Nat.le_add_left _ _).trans hcap
  have er:=readNatM_spec cap true src (R 6) (R 7) (R 5) (R 8) (R 9)
    (rn (by decide)) (rn (by decide)) (rn (by decide)) (rn (by decide))
    (rn (by decide)) (rn (by decide)) (rn (by decide)) (rn (by decide))
    (rn (by decide)) (rn (by decide)) n pre rest a hin hhead
    (hz 6) (hz 7) (hz 8) (hz 9) (by rw [hz 5,Nat.zero_add];exact hd)
  let b:=(a.seth src (pre.length+2*(natWord n).length)).setv (R 5) n
  have er' : WExec cap (readNatM true src (R 6) (R 7) (R 5) (R 8) (R 9)) a b
      ((natBitLength n+2)*(40*2^natBitLength n+40)) := by
    simpa only [stp,if_true,hz,Nat.zero_add] using er
  have eb:=bitLenM_spec cap (StagePacket.lengthRegisters R) b
    (by simp [StagePacket.lengthRegisters,StagePacket.lengthSlots,b,R.injective.eq_iff,hz])
    (by simp [StagePacket.lengthRegisters,StagePacket.lengthSlots,b,R.injective.eq_iff,hz])
    (by simp [StagePacket.lengthRegisters,StagePacket.lengthSlots,b,R.injective.eq_iff,hz])
    (by simp [StagePacket.lengthRegisters,StagePacket.lengthSlots,b,R.injective.eq_iff,hz])
    (by simp [StagePacket.lengthRegisters,StagePacket.lengthSlots,b,R.injective.eq_iff,hz])
    (by simp [StagePacket.lengthRegisters,StagePacket.lengthSlots,b];omega)
  let c:=b.setv (R 10) (natBitLength n)
  have eb' : WExec cap (bitLenM (StagePacket.lengthRegisters R)) b c (60*n+60) := by
    simpa [c,StagePacket.lengthRegisters,StagePacket.lengthSlots,b] using eb
  have ec:=addFour_spec cap (R 10) (R 2) (R 11)
    (rn (by decide)) (rn (by decide)) (rn (by decide)) c (natBitLength n) (by simp [c])
    (by simp [c,b,R.injective.eq_iff,hz])
    (by simp [c,b,R.injective.eq_iff,hz];omega)
  let d:=c.setv (R 2) (4*natBitLength n)
  have ec' : WExec cap (addFour (R 10) (R 2) (R 11)) c d (72*natBitLength n+15) := by
    simpa only [d,c,b,WState.setv_val,WState.seth_val,Function.update_self,
      Function.update_of_ne (rn (by decide : (2:Fin 16)≠10)),
      Function.update_of_ne (rn (by decide : (2:Fin 16)≠5)),hz,Nat.zero_add] using ec
  have e1:=WExec.inc (cap:=cap) (R 2) d (by simp [d];omega)
  let e:=d.setv (R 2) (4*natBitLength n+1)
  have e1' : WExec cap (.inc (R 2)) d e 3 := by simpa only [e,d,WState.setv_val,Function.update_self] using e1
  have e2:=WExec.inc (cap:=cap) (R 2) e (by simp [e];omega)
  let f:=e.setv (R 2) (4*natBitLength n+2)
  have e2' : WExec cap (.inc (R 2)) e f 3 := by simpa only [f,e,WState.setv_val,Function.update_self,Nat.add_assoc] using e2
  have ef:=wrewind_spec cap src (R 2) (4*natBitLength n+2) f (by simp [f]) (by simp [f];omega)
  let g:=(f.setv (R 2) 0).seth src (f.sh src-(4*natBitLength n+2))
  have eg:=wclear_spec cap (R 10) (natBitLength n) g
    (by simp [g,f,e,d,c,b,R.injective.eq_iff]) (by simp [g,f,e,d,c,b,R.injective.eq_iff];omega)
  refine WExec.cast cap (er'.seq (eb'.seq (ec'.seq (e1'.seq (e2'.seq (ef.seq eg)))))) ?_ ?_
  · apply WState.eq
    · funext t
      by_cases ht : t=src
      · subst t
        simp [g,f,e,d,c,b,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length,hhead]
        omega
      · simp [g,f,e,d,c,b,Function.update_of_ne ht]
    · rfl
    · funext j
      simp [g,f,e,d,c,b,Function.update_apply,R.injective.eq_iff,hz]
      split_ifs <;> simp_all
    · rfl
  · simp only [g,f,e,d,c,b,WState.setv_val,WState.seth_val,Function.update_self] at *
    unfold readFieldCost
    omega

end NearQuarticWires.StageGreedyContext
