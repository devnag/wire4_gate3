import Proof.Quartic.StagePrintTuple.UnaryField

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

/-- `lem:print`, paper/paper.tex: a computed
Cartesian dimension is serialized as its actual unary input field. -/
def emitUnaryField (K : Fin nr) (dst : Fin (ns+1)) (OP : Fin nr) : WM ns nr :=
  .seq (repeatLiteral K dst OP [true,true]) (emitPair dst OP false)

/-- `lem:print`, paper/paper.tex: one unary
input field has four physically marked bits per count and its delimiter. -/
theorem unaryField_bytes (j : ℕ) :
    marks (frame (List.replicate j true))=List.replicate (4*j) true++[true,false] := by
  simp only [Codec.frame_eq_marks,Streaming.marks_append,marks_true_replicate,
    show marks [false]=[true,false] from rfl]
  congr 2
  omega

/-- `lem:print`, paper/paper.tex: repeated
pair literals supply exactly the four marker bits per unary count. -/
theorem repeatedPair_bytes (j : ℕ) :
    marks (List.replicate j [true,true]).flatten=List.replicate (4*j) true := by
  change marks (List.replicate j (List.replicate 2 true)).flatten=_
  rw [List.flatten_replicate_replicate,marks_true_replicate]
  congr 1
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: every unary header bit is physically written from the
computed counter, with its exact marker and delimiter cost included. -/
theorem emitUnaryField_spec (cap : ℕ) (K : Fin nr) (dst : Fin (ns+1)) (OP : Fin nr)
    (hKO : K≠OP) (j : ℕ) (σ : WState ns nr)
    (hk : σ.val K=j) (hd : σ.sh dst=(σ.st dst).length)
    (hj : j≤cap) (hcap : σ.val OP+4*j+4≤cap) :
    WExec cap (emitUnaryField K dst OP) σ
      ((appendO σ dst OP (marks (frame (List.replicate j true)))).setv K 0)
      (60*(j+1)) := by
  have e1 := repeatLiteral_spec cap K dst OP hKO [true,true] j σ hk hd hj
    (by norm_num;omega)
  let d := (appendO σ dst OP (marks (List.replicate j [true,true]).flatten)).setv K 0
  have e2 := emitPair_spec cap dst OP false d
    (by simp [d,appendO,hd])
    (by simp only [d,WState.setv_val,Function.update_of_ne hKO.symm,
      appendO_val,Function.update_self,repeatedPair_bytes,List.length_replicate]
        omega)
  refine (e1.seq e2).cast cap ?_ (by norm_num;omega)
  simp only [d,appendO_setv _ _ _ K hKO,appendO_append]
  rw [unaryField_bytes,repeatedPair_bytes]

end NearQuarticWires.StageTuple
