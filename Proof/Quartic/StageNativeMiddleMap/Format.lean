import Proof.Quartic.StageNativeMiddleMap.Codec

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMiddleMap

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: direct
physical output contains both unchanged encoded metadata fields,
the actual nested framed reply and all nine final delimiters. -/
def formatProgram (P : Fin 4↪Fin (ns+1)) (OP SC K : Fin nr) : WM ns nr :=
  .seq (StageNativeKids.appendNaturalFieldReset (P 0) (P 3) OP SC K)
    (.seq (StageTuple.appendNestedFieldReset (P 1) (P 3) OP SC)
      (.seq (StageNativeKids.appendNaturalFieldReset (P 2) (P 3) OP SC K)
        (.seq (emitWordM (P 3) OP (List.replicate 8 false)) (emitC (P 3) OP false))))

theorem format_spec (cap : ℕ) (P : Fin 4↪Fin (ns+1)) (OP SC K : Fin nr)
    (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC)
    (q count : ℕ) (payload : List Bool) (a : WState ns nr)
    (hq : a.st (P 0)=natWord q) (hb : a.st (P 1)=frame payload) (hn : a.st (P 2)=natWord count)
    (hh : ∀ i : Fin 3,a.sh (P i.castSucc)=0)
    (hd : a.sh (P 3)=(a.st (P 3)).length) (hSC : a.val SC=0) (hK : a.val K=0)
    (hc : a.val OP+4*((natWord q).length+(frame payload).length+(natWord count).length)+100 ≤ cap) :
    WExec cap (formatProgram P OP SC K) a
      (appendO a (P 3) OP (frame (StagePrint.NativeMiddle.word q payload count)))
      (1000*((natWord q).length+(frame payload).length+(natWord count).length+1)) := by
  have hp {i j : Fin 4} : P i=P j ↔ i=j := P.injective.eq_iff
  have hh1 : a.sh (P 1)=0 := hh 1
  have hh2 : a.sh (P 2)=0 := hh 2
  simp only [frame_length] at hc
  have e1:=StageNativeKids.appendNaturalFieldReset_spec cap (P 0) (P 3) OP SC K
    (P.injective.ne (by decide)) hOS hKO hKS q [] a (by simpa using hq) (hh 0) hd hSC hK (by omega)
  let b:=appendO a (P 3) OP (marks (frame (natWord q)))
  have e2:=StageTuple.appendNestedFieldReset_spec cap (P 1) (P 3) OP SC
    (P.injective.ne (by decide)) hOS payload [] b
    (by simp [b,appendO,hp,hb]) (by simp [b,appendO,hp,hh1])
    (by simp [b,appendO,hd]) (by simp [b,appendO,hOS.symm,hSC])
    (by simp only [b,appendO_val,Function.update_self,Codec.marks_length,frame_length];omega)
  let c:=appendO b (P 3) OP (marks (frame (frame payload)))
  have e3:=StageNativeKids.appendNaturalFieldReset_spec cap (P 2) (P 3) OP SC K
    (P.injective.ne (by decide)) hOS hKO hKS count [] c
    (by simp [c,b,appendO,hp,hn]) (by simp [c,b,appendO,hp,hh2])
    (by simp [c,b,appendO,hd,Nat.add_assoc]) (by simp [c,b,appendO,hOS.symm,hSC])
    (by simp [c,b,appendO,hKO,hK])
    (by simp only [c,b,appendO_val,Function.update_self,Codec.marks_length,frame_length];omega)
  let d:=appendO c (P 3) OP (marks (frame (natWord count)))
  have e4:=emitWordM_spec cap (P 3) OP (List.replicate 8 false) d
    (by simp [d,c,b,appendO,hd,Nat.add_assoc])
    (by simp only [d,c,b,appendO_val,Function.update_self,Codec.marks_length,frame_length,List.length_replicate];omega)
  let e:=appendO d (P 3) OP (marks (List.replicate 8 false))
  have e5:=emitC_spec cap (P 3) OP false e
    (by simp [e,d,c,b,appendO,hd,Nat.add_assoc])
    (by simp only [e,d,c,b,appendO_val,Function.update_self,Codec.marks_length,frame_length,List.length_replicate];omega)
  change WExec cap _ e (appendO e (P 3) OP [false]) _ at e5
  refine (e1.seq (e2.seq (e3.seq (e4.seq e5)))).cast cap ?_ (by
    unfold StageTuple.appendNestedFieldCost
    simp only [List.length_replicate]
    omega)
  simp only [e,d,c,b,appendO_append,frame_word_eq,List.append_assoc]

end NearQuarticWires.StageNativeMiddleMap
