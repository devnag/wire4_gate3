import Proof.Quartic.StagePrint.TranslationMemory
import Proof.Quartic.StageRecovery.NaturalPrint

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `imp:pullback` and `lem:print`, paper/paper.tex: actual scalar values are serialized by the binary natural codec, not by a unary-value loop. -/
def emitHeaderFields : List (Fin VV)→St VV MM
  | []=>skipS
  | x::xs=>.seq (StageRecovery.emitVariable x) (emitHeaderFields xs)

/-- `imp:pullback` and `lem:print`, paper/paper.tex: only the natural codec's six scratch slots and the list-loop junk slot are modified. -/
def headerEmitScratch : List (Fin VV):=[t3,t5,t6,t7,t8,t9,vJ]

/-- `prop:time`, paper/paper.tex: each actual scalar is charged by binary length. -/
def headerEmitCost (values : List ℕ) : ℕ := (values.map (fun v=>40*natBitLength v+43)).sum+1

/-- `imp:pullback` and `lem:print`, paper/paper.tex: all actual canonical scalar fields are written while retaining the original source, memory and every nonscratch metadata value. -/
theorem emitHeaderFields_run (C : Ctx) :
    ∀ (fields : List (Fin VV)) (a : DS VV MM), Cst a→2≤C.Wd→
      (∀x∈fields,x∉headerEmitScratch)→
      (∀x∈fields,natBitLength (a.env x)+2<2^C.Wd)→
    Hs C (emitHeaderFields fields) a (headerEmitCost (fields.map a.env)) (fun b=>
      b.out=a.out++(fields.map a.env).flatMap natWord ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b headerEmitScratch)
  | [],a,hc,_hW,_hr,_hf=>by
    refine (skip_spec (C:=C) a).mono (by simp [headerEmitCost]) ?_
    rintro b rfl
    exact ⟨by simp [DS.set],rfl,Cst.of_fr hc (show Fr a (a.set vJ 0) [vJ] from
      Fr.set a _ (by simp)) (by decide),(Fr.set a _ (by simp [headerEmitScratch]))⟩
  | x::xs,a,hc,hW,hr,hf=>by
    have hx : x≠t3:=by intro h;exact hr x (by simp) (by simp [headerEmitScratch,h])
    have e1:=StageRecovery.emitVariable_spec C a hc x hx hW (hf x (by simp))
    unfold emitHeaderFields
    refine (Hs.seq (t2:=headerEmitCost (xs.map a.env)) e1 ?_).mono
      (by simp [headerEmitCost];omega) (fun _ h=>h)
    rintro b ⟨bo,bs,bc,bfr⟩
    have eb : ∀y∈xs,b.env y=a.env y := by
      intro y hy
      exact bfr y (by
        intro hh
        exact hr y (by simp [hy]) (by simpa [headerEmitScratch] using List.mem_append_left [vJ] hh))
    have eh:=emitHeaderFields_run C xs b bc hW
      (by intro y hy;exact hr y (by simp [hy]))
      (by intro y hy;rw [eb y hy];exact hf y (by simp [hy]))
    have emap : xs.map b.env=xs.map a.env:=List.map_congr_left eb
    rw [emap] at eh
    refine eh.mono le_rfl ?_
    rintro d ⟨do_,ds,dc,dfr⟩
    refine ⟨?_,ds.trans bs,dc,?_⟩
    · rw [do_,bo]
      simp [List.append_assoc]
    · exact (bfr.weaken (by intro y hy;simp only [headerEmitScratch,List.mem_cons] at *;tauto)).trans dfr

end NearQuarticWires.StagePrint.Header
