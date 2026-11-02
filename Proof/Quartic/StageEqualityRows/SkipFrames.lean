import Proof.Quartic.StageEqualityRows.Request
import Proof.Quartic.StageGamma.Unframe

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

theorem seth_twice (a : WState ns nr) (src : Fin (ns+1)) (x y : ℕ) :
    (a.seth src x).seth src y=a.seth src y := by
  apply WState.eq
  · funext i
    by_cases h:i=src
    · subst i;simp
    · simp [Function.update_of_ne h]
  · rfl
  · rfl
  · rfl

/-- `lem:print`, paper/paper.tex: an opaque
framed column is traversed by its actual marker/data pairs. -/
def skipRecord (src : Fin (ns+1)) : WM ns nr :=
  .seq (.whs src (.seq (.fwd src) (.fwd src))) (.fwd src)

theorem skipPairs_run (cap : ℕ) (src : Fin (ns+1)) (rest : List Bool) :
    ∀ (bits pre : List Bool) (a : WState ns nr),
    a.st src=pre++frame bits++rest → a.sh src=pre.length →
    WExec cap (.whs src (.seq (.fwd src) (.fwd src))) a
      (a.seth src (pre.length+2*bits.length)) (5*bits.length+1)
  | [],pre,a,hst,hsh=>by
      have hb : wbit a src=false := by
        unfold wbit readTapeBit
        rw [hst,hsh]
        simp [frame,List.getD_append_right]
      have he : a.seth src (pre.length+2*([] : List Bool).length)=a := by
        apply WState.eq
        · funext i;by_cases h:i=src
          · subst i;simp [hsh]
          · simp [Function.update_of_ne h]
        · rfl
        · rfl
        · rfl
      rw [he]
      exact WExec.whsF hb
  | bit::bits,pre,a,hst,hsh=>by
      have hb : wbit a src=true := by
        unfold wbit readTapeBit
        rw [hst,hsh]
        simp [frame,List.getD_append_right]
      have e1:=WExec.fwd (cap:=cap) src a
      have e2:=WExec.fwd (cap:=cap) src (a.seth src (a.sh src+1))
      let b:=(a.seth src (a.sh src+1)).seth src ((a.seth src (a.sh src+1)).sh src+1)
      have ht:=skipPairs_run cap src rest bits (pre++[true,bit]) b
        (by simp only [b,WState.seth_st,hst,frame,List.cons_append,List.append_assoc,List.nil_append])
        (by simp [b,hsh])
      refine (WExec.whsT hb (e1.seq e2) ht).cast cap ?_ (by simp;omega)
      simp only [b,seth_twice,List.length_cons,List.length_append,List.length_cons,List.length_nil]
      congr 1
      omega

/-- `lem:print`, paper/paper.tex: the complete
column scanner consumes its real delimiter and preserves every byte. -/
theorem skipRecord_run (cap : ℕ) (src : Fin (ns+1)) (bits pre rest : List Bool)
    (a : WState ns nr) (hst : a.st src=pre++frame bits++rest) (hsh : a.sh src=pre.length) :
    WExec cap (skipRecord src) a (a.seth src (pre.length+(frame bits).length)) (5*bits.length+3) := by
  have e1:=skipPairs_run cap src rest bits pre a hst hsh
  have e2:=WExec.fwd (cap:=cap) src (a.seth src (pre.length+2*bits.length))
  refine (e1.seq e2).cast cap ?_ (by omega)
  simp only [seth_twice,WState.seth_sh,Function.update_self,frame_length,Nat.add_assoc]

/-- `lem:print`, paper/paper.tex: the number
of actual framed columns controls the physical scan, with no supplied
header length or expanded truth table. -/
def skipRecords (src : Fin (ns+1)) (K : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (skipRecord src))

theorem skipRecords_run (cap : ℕ) (src : Fin (ns+1)) (K : Fin nr) :
    ∀ (columns : List (List Bool)) (pre rest : List Bool) (a : WState ns nr),
    a.st src=pre++columns.flatMap frame++rest → a.sh src=pre.length →
    a.val K=columns.length → columns.length≤cap →
    WExec cap (skipRecords src K) a
      ((a.seth src (pre.length+(columns.flatMap frame).length)).setv K 0)
      ((columns.map (fun bits=>5*bits.length+7)).sum+1)
  | [],pre,rest,a,hst,hsh,hK,hcap=>by
      have he : (a.seth src (pre.length+(([] : List (List Bool)).flatMap frame).length)).setv K 0=a := by
        apply WState.eq
        · funext i;by_cases h:i=src
          · subst i;simp [hsh]
          · simp [Function.update_of_ne h]
        · rfl
        · funext i;by_cases h:i=K
          · subst i;simpa using hK.symm
          · simp [Function.update_of_ne h]
        · rfl
      rw [he]
      exact WExec.whrF (by simpa using hK)
  | bits::columns,pre,rest,a,hst,hsh,hK,hcap=>by
      have e1:=WExec.dec (cap:=cap) K a (by simp only [hK,List.length_cons];omega)
      let b:=a.setv K (a.val K-1)
      have e2:=skipRecord_run cap src bits pre (columns.flatMap frame++rest) b
        (by simpa only [b,WState.setv_st,List.flatMap_cons,List.append_assoc] using hst)
        hsh
      let c:=b.seth src (pre.length+(frame bits).length)
      have e3:=skipRecords_run cap src K columns (pre++frame bits) rest c
        (by simp only [c,b,WState.seth_st,WState.setv_st,hst,List.flatMap_cons,List.append_assoc])
        (by simp [c]) (by simp [c,b,hK]) (by simp at hcap;omega)
      refine (WExec.whrT (by simp [hK]) (e1.seq e2) e3).cast cap ?_ ?_
      · simp only [c,b,WState.seth_val,WState.setv_st,List.flatMap_cons,List.length_append,
          seth_twice,wsetv_setv,List.length_append]
        apply WState.eq
        · funext i;by_cases h:i=src
          · subst i;simp;omega
          · simp [Function.update_of_ne h]
        · rfl
        · funext i;by_cases h:i=K
          · subst i;simp
          · simp [Function.update_of_ne h]
        · rfl
      · simp only [List.map_cons,List.sum_cons]
        omega

end NearQuarticWires.StageEqualityRows
