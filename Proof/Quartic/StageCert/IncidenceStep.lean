import Proof.Quartic.StageCert.IncidenceReset
import Proof.Quartic.StageCert.IncidenceEmit

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearQuarticWires.StagePrep
open NearCubicWires.RepairRepresentation (natWord)

/-- `sec:algorithm`, paper/paper.tex: the outer incidence scan
retains the original coordinate count independently of the call parser. -/
def arity : Fin VV := ⟨98,by decide⟩

/-- `sec:algorithm`, paper/paper.tex: one numeric coordinate
record contains its actual raw incidence and inclusive heavy flag. -/
def coordinateRecord (c : Call) (dstar : ℕ) (i : Fin c.n) : List Bool :=
  natWord (Cells.incidence (c.first.gates++c.second.gates) i)++
    natWord (bnat (dstar≤Cells.incidence (c.first.gates++c.second.gates) i))

/-- `sec:cells`, paper/paper.tex: a coordinate incidence is
bounded by the physically encoded raw call, including any retained suffix. -/
theorem incidence_le_source_length (C : Ctx) (c : Call) (suffix : List Bool)
    (hcw : C.cw=callWord c++suffix) (i : Fin c.n) :
    Cells.incidence (c.first.gates++c.second.gates) i≤C.cw.length := by
  have h1 : Cells.incidence c.first.gates i≤(circuitWord c.first).length := by
    rw [←coordinateSum_eq_incidence]
    exact (coordinateSum_le_charge _ _).trans (wires_le_circuitWord _)
  have h2 : Cells.incidence c.second.gates i≤(circuitWord c.second).length := by
    rw [←coordinateSum_eq_incidence]
    exact (coordinateSum_le_charge _ _).trans (wires_le_circuitWord _)
  have hword := congrArg List.length (callWord_eq c)
  simp only [List.length_append] at hword
  rw [incidence_append,hcw,List.length_append]
  omega

/-- `sec:algorithm`, paper/paper.tex: the full coordinate step
resets its source scan, derives incidence and heavy flag, emits both exact
numeric records, and advances the original-coordinate counter. -/
def coordinateStep : St VV := .seq resetCoordinate
  (.seq readHeavyCoordinate (.seq emitCoordinateRecord (.op (.inc coordinate))))

/-- `sec:algorithm`, paper/paper.tex: the complete arithmetic
frame of one original-coordinate iteration. -/
def stepScratch : List (Fin VV) := coordinate::heavyBit::vPOS::censusTotal::
  (callScratch++(t3::emitNatT))

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the concrete source iteration writes exactly one incidence/heavy
record, with a uniform polynomial bit cost and no incidence oracle. -/
theorem coordinateStep_run (C : Ctx) (c : Call) (suffix : List Bool) (i : Fin c.n)
    (a : DS VV) (hc : Cst a) (hcoord : a.env coordinate=i.val)
    (hcw : C.cw=callWord c++suffix) (hW : 2*C.cw.length+8≤C.Wd)
    (hL : 2*C.cw.length+4<2^C.Wd) (hn : c.n<2^C.Wd) :
    Hs C coordinateStep a (2000*(C.cw.length+2)^3) (fun b =>
      b.out=a.out++coordinateRecord c (a.env heavyThreshold) i ∧
      b.env coordinate=i.val+1 ∧ b.wq=a.wq ∧ Cst b ∧ Fr a b stepScratch) := by
  have hdegree := incidence_le_source_length C c suffix hcw i
  have hheight : natBitLength (Cells.incidence (c.first.gates++c.second.gates) i)≤C.cw.length+1 :=
    (Nat.add_le_add_right (Nat.log_le_self 2 _) 1).trans (by omega)
  unfold coordinateStep
  apply Hx.hs
  refine Hs.then (resetCoordinate_run C a hc) (fun r ⟨_re,rc,rt,rw,ro,rconst,rf⟩ n1 hn1 => ?_)
  have ri : r.env coordinate=i.val := (rf _ (by decide)).trans hcoord
  refine Hs.then (readHeavyCoordinate_prefix_run C c i suffix r rconst rc rt ri hcw hW hL)
    (fun s ⟨st,sh,_sc,sw,so,sconst,sf⟩ n2 hn2 => ?_)
  have hd : natBitLength (s.env censusTotal)+2<2^C.Wd := by rw [st]; omega
  have hh : natBitLength (s.env heavyBit)≤2 := by
    rw [sh]
    unfold bnat
    cases decide (r.env heavyThreshold≤Cells.incidence (c.first.gates++c.second.gates) i) <;>
      norm_num [natBitLength]
  refine Hs.then (emitCoordinateRecord_run C s sconst (by omega) hd (by omega))
    (fun t ⟨tout,_tc,tw,tconst,tf⟩ n3 hn3 => ?_)
  have ti : t.env coordinate=i.val := (tf _ (by decide)).trans ((sf _ (by decide)).trans ri)
  refine Hs.last (hs_inc C coordinate t (by rw [ti]; have := i.isLt; omega)) ?_
  rintro u rfl n4 hn4
  have rH : r.env heavyThreshold=a.env heavyThreshold := rf _ (by decide)
  refine ⟨⟨?_,by simp [ti],tw.trans (sw.trans rw),?_,?_⟩,?_⟩
  · change t.out=_
    rw [tout,so,ro,st,sh,rH]
    simp only [coordinateRecord,List.append_assoc]
  · refine Cst.of_fr (T := [coordinate]) tconst (Fr.set _ _ (by simp)) (by decide) ?_
    rw [DS.set_env_ne _ _ (by decide)]
    exact tconst.pos
  · exact (rf.weaken (by simp only [stepScratch,List.mem_cons,List.mem_append]; tauto)).trans
      ((sf.weaken (by simp only [stepScratch,List.mem_cons,List.mem_append]; tauto)).trans
        ((tf.weaken (by simp only [stepScratch,List.mem_cons,List.mem_append]; tauto)).trans
          (Fr.set _ _ (by simp [stepScratch]))))
  · have hheight' : natBitLength (s.env censusTotal)≤C.cw.length+1 := by rw [st]; exact hheight
    have hp : C.cw.length+2≤(C.cw.length+2)^3 := Nat.le_self_pow (by norm_num) _
    have hpos : 1≤(C.cw.length+2)^3 := Nat.pow_pos (by omega)
    nlinarith only [hn1,hn2,hn3,hn4,hheight',hh,hp,hpos]

end NearQuarticWires.StageCert.Incidence
