import Proof.Quartic.StagePrintTuple.UnaryScalar
import Proof.Wire_3_5.FinalPassHashTable

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a persistent
computed tuple dimension is copied to scratch before its unary field
is written, retaining the dimension for subsequent Cartesian steps. -/
def copyUnaryField (A K T : Fin nr) (dst : Fin (ns+1)) (OP : Fin nr) : WM ns nr :=
  .seq (wcopyR A K T) (emitUnaryField K dst OP)

/-- `lem:print` and `prop:time`, paper/paper.tex: the copied unary field preserves every persistent
counter and restores both scratch registers, at its actual linear cost. -/
theorem copyUnaryField_spec (cap : ℕ) (A K T : Fin nr) (dst : Fin (ns+1)) (OP : Fin nr)
    (hAK : A≠K) (hAT : A≠T) (hKT : K≠T) (hKO : K≠OP)
    (σ : WState ns nr) (hK : σ.val K=0) (hT : σ.val T=0)
    (hd : σ.sh dst=(σ.st dst).length) (hj : σ.val A≤cap)
    (hcap : σ.val OP+4*σ.val A+4≤cap) :
    WExec cap (copyUnaryField A K T dst OP) σ
      (appendO σ dst OP (marks (frame (List.replicate (σ.val A) true))))
      (100*(σ.val A+1)) := by
  have e1 := wcopyR_spec cap A K T hAK hAT hKT σ hK hT hj
  let d := σ.setv K (σ.val A)
  have e2 := emitUnaryField_spec cap K dst OP hKO (σ.val A) d
    (by simp [d]) (by simpa [d] using hd) hj
    (by simpa [d,Function.update_of_ne hKO.symm] using hcap)
  refine (e1.seq e2).cast cap ?_ (by omega)
  apply WState.eq
  · rfl
  · rfl
  · funext i
    by_cases hi : i=K
    · subst i;simp [d,appendO,hKO,hK]
    · by_cases hiO : i=OP
      · subst i;simp [d,appendO,hKO.symm]
      · simp [d,appendO,Function.update_of_ne hi,Function.update_of_ne hiO,hKO.symm]
  · rfl

/-- `lem:print`, paper/paper.tex: the four
Cartesian or Stack dimension fields are emitted in their actual fixed
codec order from their persistent computed registers. -/
def unaryHeaderProgram (rs : List (Fin nr)) (K T : Fin nr)
    (dst : Fin (ns+1)) (OP : Fin nr) : WM ns nr :=
  match rs with
  | [] => .skip
  | A::tail => .seq (copyUnaryField A K T dst OP) (unaryHeaderProgram tail K T dst OP)

/-- `lem:print`, paper/paper.tex: each computed
unary scalar contributes its existing framed input field, in order. -/
def unaryHeaderBytes (values : List ℕ) : List Bool :=
  values.flatMap (fun j=>marks (frame (List.replicate j true)))

/-- `prop:time`, paper/paper.tex: all unary
header copying and serialization costs are linear in their real values. -/
def unaryHeaderCost (values : List ℕ) : ℕ :=
  110*((values.map (fun j=>j+1)).sum+1)

/-- `lem:print` and `prop:time`, paper/paper.tex: actual unary header serialization preserves every
input dimension and restores its two scratch registers. -/
theorem unaryHeaderProgram_spec (cap : ℕ) (rs : List (Fin nr)) (K T : Fin nr)
    (dst : Fin (ns+1)) (OP : Fin nr)
    (hKT : K≠T) (hKO : K≠OP) (hTO : T≠OP)
    (hA : ∀ A∈rs,A≠K ∧ A≠T ∧ A≠OP)
    (σ : WState ns nr) (hK : σ.val K=0) (hT : σ.val T=0)
    (hd : σ.sh dst=(σ.st dst).length)
    (hcap : σ.val OP+4*((rs.map (fun A=>σ.val A+1)).sum)+4≤cap) :
    WExec cap (unaryHeaderProgram rs K T dst OP) σ
      (appendO σ dst OP (unaryHeaderBytes (rs.map σ.val)))
      (unaryHeaderCost (rs.map σ.val)) := by
  induction rs generalizing σ with
  | nil =>
    simpa [unaryHeaderProgram,unaryHeaderBytes,unaryHeaderCost,appendO_nil] using
      ((WExec.skip (cap:=cap) σ).cast cap rfl (show 0≤110 by omega))
  | cons A tail ih =>
    obtain ⟨hAK,hAT,hAO⟩ := hA A (by simp)
    have hs : ∀B∈tail,B≠K ∧ B≠T ∧ B≠OP := fun B hB=>hA B (by simp [hB])
    have e1 := copyUnaryField_spec cap A K T dst OP hAK hAT hKT hKO σ hK hT hd
      (by simp only [List.map_cons,List.sum_cons] at hcap;omega)
      (by simp only [List.map_cons,List.sum_cons] at hcap;omega)
    let d := appendO σ dst OP (marks (frame (List.replicate (σ.val A) true)))
    have hv : ∀B∈tail,d.val B=σ.val B := by
      intro B hB
      simp [d,appendO,(hs B hB).2.2]
    have hm : tail.map (fun B=>d.val B+1)=tail.map (fun B=>σ.val B+1) :=
      List.map_congr_left (fun B hB=>congrArg (fun x : ℕ=>x+1) (hv B hB))
    have hm' : tail.map d.val=tail.map σ.val := List.map_congr_left hv
    have e2 := ih hs d
      (by simp [d,appendO,hKO,hK]) (by simp [d,appendO,hTO,hT])
      (by simp [d,appendO,hd]) (by
        rw [hm]
        simp only [d,appendO_val,Function.update_self,NearCubicGates.Close.Codec.marks_length,
          NearCubicGates.Close.Codec.frame_eq_marks,List.length_append,List.length_singleton,
          List.length_replicate]
        simp only [List.map_cons,List.sum_cons] at hcap
        omega)
    rw [hm'] at e2
    refine (e1.seq e2).cast cap ?_ ?_
    · simp [d,appendO_append,unaryHeaderBytes,List.append_assoc]
    · simp only [unaryHeaderCost,List.map_cons,List.sum_cons,List.map_map]
      omega

end NearQuarticWires.StageTuple
