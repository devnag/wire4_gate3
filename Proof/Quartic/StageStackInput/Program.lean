import Proof.Quartic.StageStackInput.Constants

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageStackInput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicGates.Close
open NearCubicGates.Close.WordPrograms.SInt (encS)
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: build the actual
cold Stack request from only the current tuple segment, genuine cached
fields and persistent computed dimensions; restore every source head. -/
def stackInputProgram (P : Fin 5↪Fin (ns+1)) (R : Fin 8↪Fin nr) : WM ns nr :=
  .seq (appendRecordFieldReset (P 0) (P 4) (R 0) (R 1))
    (.seq (cachedFramesProgram (cacheSources P) (P 4) (R 0) (R 1))
      (.seq (unaryHeaderProgram [R 4,R 5,R 6,R 7] (R 2) (R 3) (P 4) (R 0))
        (.seq (emitWordM (P 4) (R 0) [false])
          (.seq (emitC (P 4) (R 0) false) (WM.rewind (P 4) (R 0))))))

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact chosen formatter satisfies Tuple's checked
physical contract. The clock and capacity depend on the current segment
and actual fields/dimensions, never on the retained history prefix. -/
theorem stackInputProgram_spec :
    StageTuple.StackInputSpec (ns:=ns) (nr:=nr) stackInputProgram := by
  intro cap P R r pre σ ht hth hzsrc hcsrc h2src hheads hd hz hv hcap
  have hp {i j : Fin 5} : P i=P j↔i=j := P.injective.eq_iff
  have hr {i j : Fin 8} : R i=R j↔i=j := R.injective.eq_iff
  have h0 : σ.val (R 0)=0 := hz 0
  have h1 : σ.val (R 1)=0 := hz 1
  have h2 : σ.val (R 2)=0 := hz 2
  have h3 : σ.val (R 3)=0 := hz 3
  have hdh : σ.sh (P 4)=0 := hheads 3
  change 400*((tupleBytes r).length+r.W+r.m*(r.s+1)+(r.s+1)+r.m+r.tuples.length+10)≤cap at hcap
  have et:=appendRecordFieldReset_spec cap (P 0) (P 4) (R 0) (R 1)
    (P.injective.ne (by decide)) (R.injective.ne (by decide))
    (fieldRecords (r.W+1) (r.tuples.map List.flatten)) pre [false]
    (fieldRecords_nonempty _ (by omega) _) rfl σ ht hth (by rw [hdh,hd];rfl) h1
    (by rw [h0];change 0+4*(tupleBytes r).length+10≤cap;omega)
  let a:=appendO σ (P 4) (R 0) (marks (frame (tupleBytes r++[false])))
  have av : a.val (R 0)=4*(tupleBytes r).length+6 := by
    simp only [a,appendO_val,Function.update_self,h0,Codec.marks_length,frame_length,
      List.length_append,List.length_singleton]
    omega
  have ec:=copyConstants_spec cap P (R 0) (R 1) (R.injective.ne (by decide)) r a
    (by simp [a,appendO,hp,hzsrc]) (by simp [a,appendO,hp,hcsrc])
    (by simp [a,appendO,hp,h2src])
    (by simpa [a,appendO,hp] using hheads 0)
    (by simpa [a,appendO,hp] using hheads 1)
    (by simpa [a,appendO,hp] using hheads 2)
    (by simp [a,appendO,hdh,hd]) (by simp [a,appendO,hr,h1])
    (by rw [av];omega)
  let b:=appendO a (P 4) (R 0) (cachedFramesBytes (constantFields r))
  have bv : b.val (R 0)=4*(tupleBytes r).length+40*r.W+76 := by
    simp only [b,appendO_val,Function.update_self]
    change a.val (R 0)+((constantFields r).flatMap (fun bits=>marks (frame bits))).length=_
    rw [av,constantFields_length]
    omega
  have bvals : [R 4,R 5,R 6,R 7].map b.val=dimensions r := by
    simpa [b,a,appendO,hr,dimensions] using hv
  have en:=unaryHeaderProgram_spec cap [R 4,R 5,R 6,R 7] (R 2) (R 3) (P 4) (R 0)
    (R.injective.ne (by decide)) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (by
      intro A hA
      have hm : A=R 4∨A=R 5∨A=R 6∨A=R 7 := by simpa using hA
      rcases hm with hm|hm|hm|hm <;> subst A <;> simp [hr]) b
    (by simp [b,a,appendO,hr,h2]) (by simp [b,a,appendO,hr,h3])
    (by simp [b,a,appendO,hdh,hd,List.length_append,Nat.add_assoc]) (by
      have hm:=congrArg (fun ls : List ℕ=>(ls.map (fun j=>j+1)).sum) bvals
      simp only [List.map_map,Function.comp_def] at hm
      rw [hm,bv]
      simp only [dimensions,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      omega)
  rw [bvals] at en
  let c:=appendO b (P 4) (R 0) (unaryHeaderBytes (dimensions r))
  have cv : c.val (R 0)=4*(tupleBytes r).length+40*r.W+
      4*(r.m*(r.s+1)+(r.s+1)+r.m+r.tuples.length)+84 := by
    simp only [c,appendO_val,Function.update_self,unaryBytes_length]
    rw [bv]
    simp only [dimensions,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have ee:=emitWordM_spec cap (P 4) (R 0) [false] c
    (by simp [c,b,a,appendO,hdh,hd,List.length_append,Nat.add_assoc])
    (by rw [cv];norm_num only [List.length_cons,List.length_nil];omega)
  let d:=appendO c (P 4) (R 0) (marks [false])
  have ed:=Codec.emitBit_spec cap (P 4) (R 0) false d
    (by simp [d,c,b,a,appendO,hdh,hd,List.length_append,Nat.add_assoc])
    (by simp only [d,appendO_val,Function.update_self,Codec.marks_length,
      List.length_cons,List.length_nil];rw [cv];omega)
  let e:=appendO d (P 4) (R 0) [false]
  have he : e=appendO σ (P 4) (R 0) (frame r.word) := by
    simp only [e,d,c,b,a,appendO_append,stackInput_frame,cachedFramesBytes,List.append_assoc]
  have hlen : (frame r.word).length=c.val (R 0)+3 := by
    rw [stackInput_length,cv]
  have ecap : (frame r.word).length≤cap := by
    rw [hlen,cv]
    omega
  have er:=wrewind_spec cap (P 4) (R 0) (frame r.word).length e
    (by rw [he];simp [appendO,h0])
    (by rw [he];simp only [appendO_val,Function.update_self,h0,Nat.zero_add];exact ecap)
  refine (et.seq (ec.seq (en.seq (ee.seq (ed.seq er))))).cast cap ?_ ?_
  · rw [he]
    apply WState.eq
    · funext i
      by_cases hi : i=P 4
      · subst i;simp [appendO,hdh]
      · simp [appendO,Function.update_of_ne hi]
    · simp [appendO,hd]
    · funext i
      by_cases hi : i=R 0
      · subst i;simp [appendO,h0]
      · simp [appendO,Function.update_of_ne hi]
    · rfl
  · rw [constantCost,hlen,cv]
    unfold appendRecordFieldCost unaryHeaderCost stackInputMagnitude
    simp only [dimensions,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.length_cons,List.length_nil]
    change _≤10000*((tupleBytes r).length+r.W+r.m*(r.s+1)+(r.s+1)+r.m+r.tuples.length+10)
    dsimp only [tupleBytes]
    omega

end NearQuarticWires.StageStackInput
