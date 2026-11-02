import Proof.Quartic.StageTupleInputs.SupportBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTupleInputs

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.Interfaces
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: copy persistent
J/M counters through the real writer bank, then copy only the actual
remaining variable codecs at the already parsed support cursor. -/
def supportInputProgram (P : Fin 2↪Fin (ns+1)) (R : Fin 9↪Fin nr)
    (J M : Fin nr) : WM ns nr :=
  .seq (counterHeaderProgram J R (P 1))
    (.seq (counterHeaderProgram M R (P 1))
      (.seq (appendPayloadReset (P 0) (P 1) (R 7) (R 8))
        (.seq (emitC (P 1) (R 7) false) (WM.rewind (P 1) (R 7)))))

/-- `lem:print` and `prop:time`, paper/paper.tex: the existing support-index packet is physically built
with no extra source field or decoded atom, retaining the real parsed
source cursor and every persistent/exterior state component. -/
theorem supportInputProgram_spec :
    StageTuple.SupportInputSpec (ns:=ns) (nr:=nr) supportInputProgram := by
  intro cap P R J M r σ hRJ hRM hsrc hsrch hout houth hz hJ hM hcap
  have hp {i j : Fin 2} : P i=P j↔i=j := P.injective.eq_iff
  have hr {i j : Fin 9} : R i=R j↔i=j := R.injective.eq_iff
  let V:=supportInputMagnitude r
  have hV : 20≤V := (supportMagnitude_bounds r).2.2.2
  have hmV : r.support.length+1≤V := (supportMagnitude_bounds r).1
  have hjV : r.index.val+1≤V := (supportMagnitude_bounds r).2.1
  have hbV : (r.support.flatMap natWord).length≤V := (supportMagnitude_bounds r).2.2.1
  have hjb:=bitLength_le r.index.val
  have hmb:=bitLength_le r.support.length
  change 1000*V≤cap at hcap
  have h7 : σ.val (R 7)=0 := hz 7
  have h8 : σ.val (R 8)=0 := hz 8
  have hjlen : (marks (natWord r.index.val)).length≤4*r.index.val+6 := by
    simp only [Codec.marks_length,NearCubicGates.Close.Dispatch.natWord_length]
    omega
  have hmlen : (marks (natWord r.support.length)).length≤4*r.support.length+6 := by
    simp only [Codec.marks_length,NearCubicGates.Close.Dispatch.natWord_length]
    omega
  have ej:=counterHeaderProgram_spec cap J R (P 1) hRJ σ
    (by intro i _;exact hz i) (by rw [houth,hout];rfl)
    (by rw [hJ,h7];omega)
  rw [hJ] at ej
  let a:=appendO σ (P 1) (R 7) (marks (natWord r.index.val))
  have am : a.val M=r.support.length := by
    simp only [a,appendO_val,Function.update_of_ne (hRM 7).symm,hM]
  have av : a.val (R 7)=(marks (natWord r.index.val)).length := by
    simp only [a,appendO_val,Function.update_self,h7,Nat.zero_add]
  have az : ∀i:Fin 9,i.val<7→a.val (R i)=0 := by
    intro i hi
    have hi7 : i≠7 := by intro he;subst i;norm_num at hi
    simp [a,appendO,hr,hi7,hz i]
  have em:=counterHeaderProgram_spec cap M R (P 1) hRM a az
    (by simp [a,appendO,houth,hout]) (by rw [am,av];omega)
  rw [am] at em
  let b:=appendO a (P 1) (R 7) (marks (natWord r.support.length))
  have bv : b.val (R 7)=(marks (natWord r.index.val)).length+
      (marks (natWord r.support.length)).length := by
    simp only [b,appendO_val,Function.update_self,av]
  have bsrc : b.st (P 0)=marks (natWord r.support.length)++
      frame (r.support.flatMap natWord)++[] := by
    simp [b,a,appendO,hp,hsrc,supportSource_split]
  have bsh : b.sh (P 0)=(marks (natWord r.support.length)).length := by
    simp [b,a,appendO,hp,hsrch]
  have ep:=appendPayloadAtReset_spec cap (P 0) (P 1) (R 7) (R 8)
    (P.injective.ne (by decide)) (R.injective.ne (by decide))
    (r.support.flatMap natWord) (marks (natWord r.support.length)) [] b bsrc bsh
    (by simp [b,a,appendO,houth,hout,List.length_append,Nat.add_assoc])
    (by simp [b,a,appendO,hr,h8]) (by rw [bv];omega)
  let c:=appendO b (P 1) (R 7) (marks (r.support.flatMap natWord))
  have cv : c.val (R 7)=(marks (natWord r.index.val)).length+
      (marks (natWord r.support.length)).length+2*(r.support.flatMap natWord).length := by
    simp only [c,appendO_val,Function.update_self,Codec.marks_length,bv]
  have ed:=Codec.emitBit_spec cap (P 1) (R 7) false c
    (by simp [c,b,a,appendO,houth,hout,List.length_append,Nat.add_assoc])
    (by rw [cv];omega)
  let d:=appendO c (P 1) (R 7) [false]
  have hd : d=appendO σ (P 1) (R 7) (frame r.word) := by
    simp only [d,c,b,a,appendO_append,supportInput_frame,List.append_assoc]
  have hlen : (frame r.word).length≤8*V := supportPacket_length r
  have hlen' : (frame r.word).length=c.val (R 7)+1 := by
    rw [supportInput_frame,cv]
    simp only [List.length_append,List.length_singleton,Codec.marks_length]
  have er:=wrewind_spec cap (P 1) (R 7) (frame r.word).length d
    (by rw [hd];simp [appendO,h7])
    (by rw [hd];simp only [appendO_val,Function.update_self,h7,Nat.zero_add];omega)
  refine (ej.seq (em.seq (ep.seq (ed.seq er)))).cast cap ?_ ?_
  · rw [hd]
    apply WState.eq
    · funext i
      by_cases hi:i=P 1
      · subst i;simp [appendO,houth]
      · simp [appendO,Function.update_of_ne hi]
    · simp [appendO,hout]
    · funext i
      by_cases hi:i=R 7
      · subst i;simp [appendO,h7]
      · simp [appendO,Function.update_of_ne hi]
    · rfl
  · have hjcost:=counterHeaderCost_bound r.index.val V hjV hV
    have hmcost:=counterHeaderCost_bound r.support.length V hmV hV
    unfold appendPayloadCost
    change _≤10000*V^2
    nlinarith only [hjcost,hmcost,hlen,hbV,hV]

end NearQuarticWires.StageTupleInputs
