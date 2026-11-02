import Proof.Quartic.StagePrintTuple.UnaryBytes

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicGates.Close

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the current
actual original-child counter is serialized directly into its nested
unary input field, without constructing an intermediate index tape. -/
def emitNestedUnary (K : Fin nr) (dst : Fin (ns+1)) (OP : Fin nr) : WM ns nr :=
  .seq (repeatLiteral K dst OP [true,true,true,true])
    (.seq (emitWordM dst OP [true,false]) (emitPair dst OP false))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual counter produces every bit of its required
nested unary child-index field, consuming only its working counter. -/
theorem emitNestedUnary_spec (cap : ℕ) (K : Fin nr) (dst : Fin (ns+1)) (OP : Fin nr)
    (hKO : K≠OP) (j : ℕ) (σ : WState ns nr)
    (hk : σ.val K=j) (hd : σ.sh dst=(σ.st dst).length)
    (hj : j≤cap) (hcap : σ.val OP+8*j+8≤cap) :
    WExec cap (emitNestedUnary K dst OP) σ
      ((appendO σ dst OP (marks (frame (frame (List.replicate j true))))).setv K 0)
      (100*(j+1)) := by
  have e1 := repeatLiteral_spec cap K dst OP hKO [true,true,true,true] j σ hk hd hj
    (by norm_num;omega)
  let d := (appendO σ dst OP (marks (List.replicate j [true,true,true,true]).flatten)).setv K 0
  have e2 := emitWordM_spec cap dst OP [true,false] d
    (by simp [d,appendO,hd])
    (by simp only [d,WState.setv_val,Function.update_of_ne hKO.symm,
      appendO_val,Function.update_self,repeatedQuadruple_bytes,List.length_replicate]
        norm_num
        omega)
  let e := appendO d dst OP (marks [true,false])
  have e3 := emitPair_spec cap dst OP false e
    (by simp [e,d,appendO,hd,Nat.add_assoc])
    (by simp only [e,appendO_val,Function.update_self,d,WState.setv_val,
      Function.update_of_ne hKO.symm,appendO_val,repeatedQuadruple_bytes,List.length_replicate]
        norm_num [marks]
        omega)
  refine (e1.seq (e2.seq e3)).cast cap ?_ (by norm_num;omega)
  simp only [e,d,appendO_setv _ _ _ K hKO,appendO_append]
  rw [nestedUnary_bytes,repeatedQuadruple_bytes]
  simp [marks,List.append_assoc]

end NearQuarticWires.StageTuple
