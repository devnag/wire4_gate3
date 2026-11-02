import Proof.Quartic.StageGreedyContext.MeasuredField

/-!
# The original arity prefix is physically obtained from the preparation

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGreedyContext

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

variable {ns nr : ℕ}

/-- `lem:print` and `prop:time`, paper/paper.tex: the original arity is read from
the actual prepared source, its head is restored, and its literal
marked natural word begins the one common context frame. -/
def arityPrefix (src dst : Fin (ns+1)) (R : Fin 16 ↪ Fin nr) : WM ns nr :=
  .seq (WM.clear (R 2)) (.seq (WM.clear (R 10))
    (.seq (.fwd src) (.seq (.fwd src) (.seq (readFieldRestore src R)
      (.seq (.bwd src) (.seq (.bwd src) (writeNatM dst (StagePacket.lengthRegisters R))))))))

/-- `prop:time`, paper/paper.tex: the
actual arity-prefix cost includes both preparation counters, its
finite decoder, measured return and literal scalar writer. -/
def arityPrefixCost (a : WState ns nr) (R : Fin 16 ↪ Fin nr) (n : ℕ) : ℕ :=
  3*a.val (R 2)+3*a.val (R 10)+readFieldCost n+
    (natBitLength n+10)*(100*n+200)+50

/-- `lem:print`, paper/paper.tex: the
exact final state of the arity pass retains all original tapes and
registers outside its finite counter and marked output updates. -/
def arityPrefixState (dst : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (a : WState ns nr) (n : ℕ) : WState ns nr :=
  appendO (((a.setv (R 2) 0).setv (R 10) 0).setv (R 5) n) dst (R 13)
    (Streaming.marks (natWord n))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual finite arity pass returns
the prepared source head to zero and writes its binary arity prefix,
without accessing the original carrier's count or entry suffix. -/
theorem arityPrefix_spec (cap : ℕ) (src dst : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (_hsd : src≠dst) (n : ℕ) (rest : List Bool) (a : WState ns nr)
    (hin : a.st src=frame (true::(natWord n++rest))) (hhead : a.sh src=0)
    (hout : a.st dst=[]) (hdhead : a.sh dst=0)
    (hz : ∀j : Fin 16,j≠2→j≠10→a.val (R j)=0)
    (hcap : a.val (R 2)+a.val (R 10)+20*(n+natBitLength n+1)+2^(natBitLength n+1)≤cap) :
    WExec cap (arityPrefix src dst R) a (arityPrefixState dst R a n) (arityPrefixCost a R n) := by
  have rn {i j : Fin 16} (h : i≠j) : R i≠R j:=R.injective.ne h
  have hl : 20*(n+natBitLength n+1)+2^(natBitLength n+1)≤cap:=by omega
  have hab : a.val (R 2)+a.val (R 10)≤cap :=
    (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hcap)
  have ha2 : a.val (R 2)≤cap := (Nat.le_add_right _ _).trans hab
  have ha10 : a.val (R 10)≤cap := (Nat.le_add_left _ _).trans hab
  have ec2:=wclear_spec cap (R 2) (a.val (R 2)) a rfl ha2
  let b:=a.setv (R 2) 0
  have ec10:=wclear_spec cap (R 10) (a.val (R 10)) b
    (by simp [b,R.injective.eq_iff]) (by simpa [b,R.injective.eq_iff] using ha10)
  let c:=b.setv (R 10) 0
  have cz : ∀j : Fin 16,c.val (R j)=0:=by
    intro j
    by_cases h2 : j=2
    · subst j;simp [c,b,R.injective.eq_iff]
    · by_cases h10 : j=10
      · subst j;simp [c]
      · simp [c,b,Function.update_apply,R.injective.eq_iff,h2,h10,hz j h2 h10]
  have ef1:=WExec.fwd (cap:=cap) src c
  let d:=c.seth src 1
  have ef1' : WExec cap (.fwd src) c d 1 := by simpa [d,c,b,hhead] using ef1
  have ef2:=WExec.fwd (cap:=cap) src d
  let e:=d.seth src 2
  have ef2' : WExec cap (.fwd src) d e 1 := by simpa [e,d] using ef2
  have er:=readFieldRestore_spec cap src R n [true,true] (Streaming.marks rest++[false]) e
    (by simp [e,d,c,b,hin,NearCubicGates.Close.Codec.frame_eq_marks,
      Streaming.marks, List.flatMap_append,List.append_assoc])
    (by simp [e]) (by intro j;exact cz j) hl
  let f:=e.setv (R 5) n
  have eb1:=WExec.bwd (cap:=cap) src f
  let g:=f.seth src 1
  have eb1' : WExec cap (.bwd src) f g 1 := by simpa [g,f,e] using eb1
  have eb2:=WExec.bwd (cap:=cap) src g
  let h:=g.seth src 0
  have eb2' : WExec cap (.bwd src) g h 1 := by simpa [h,g] using eb2
  have heq : h=c.setv (R 5) n := by
    apply WState.eq
    · funext t
      by_cases ht : t=src
      · subst t;simp [h,g,f,e,d,c,b,hhead]
      · simp [h,g,f,e,d,Function.update_of_ne ht]
    · rfl
    · rfl
    · rfl
  have hn : h.val (R 5)=n := by rw [heq];simp
  have hzH (j : Fin 16) (hj : j≠5) : h.val (R j)=0 := by
    rw [heq,WState.setv_val,Function.update_of_ne (rn hj)]
    exact cz j
  have ew:=writeNatM_spec cap dst (StagePacket.lengthRegisters R) h
    (by exact hzH 6 (by decide)) (by exact hzH 7 (by decide))
    (by exact hzH 8 (by decide)) (by exact hzH 10 (by decide))
    (by exact hzH 12 (by decide)) (by exact hzH 9 (by decide))
    (by simp [heq,c,b,hout,hdhead])
    (by change h.val (R 5)+h.val (R 13)+6*natBitLength (h.val (R 5))+6≤cap
        have small (x y : ℕ) : x+6*y+6≤20*(x+y+1) := by omega
        have hg : n+6*natBitLength n+6≤cap :=
          (small n (natBitLength n)).trans ((Nat.le_add_right _ _).trans hl)
        simpa only [hn,hzH 13 (by decide),Nat.add_zero] using hg)
  have ew' : WExec cap (writeNatM dst (StagePacket.lengthRegisters R)) h
      (appendO h dst (R 13) (Streaming.marks (natWord n)))
      ((natBitLength n+10)*(100*n+200)) := by
    change WExec cap (writeNatM dst (StagePacket.lengthRegisters R)) h
      (appendO h dst (R 13) (Streaming.marks (natWord (h.val (R 5)))))
      ((natBitLength (h.val (R 5))+10)*(100*h.val (R 5)+200)) at ew
    simpa only [hn] using ew
  refine WExec.cast cap (ec2.seq (ec10.seq (ef1'.seq (ef2'.seq (er.seq (eb1'.seq (eb2'.seq ew'))))))) ?_ ?_
  · rw [heq]
    rfl
  · unfold arityPrefixCost
    omega

end NearQuarticWires.StageGreedyContext
