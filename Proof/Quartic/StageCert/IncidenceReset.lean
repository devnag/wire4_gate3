import Proof.Quartic.StageCert.IncidenceHeavy

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearQuarticWires.StagePrep

/-- `sec:algorithm`, paper/paper.tex: each new coordinate starts
at the original public call cursor with a fresh incidence accumulator. -/
def resetCoordinate : St VV := .seq (.op .rstC)
  (.seq (.op (.zero vPOS)) (.op (.zero censusTotal)))

/-- `sec:algorithm`, paper/paper.tex: exact reset state for one
new original-coordinate incidence scan. -/
def resetState (a : DS VV) : DS VV :=
  (({a with cp:=0}).set vPOS 0).set censusTotal 0

/-- `sec:algorithm`, paper/paper.tex: resetting the public call
cursor and incidence accumulator has constant physical cost and preserves
the witness cursor, output and all other arithmetic registers. -/
theorem resetCoordinate_run (C : Ctx) (a : DS VV) (hc : Cst a) :
    Hs C resetCoordinate a 5 (fun b =>
      b=resetState a ∧ b.cp=0 ∧ b.env censusTotal=0 ∧
      b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ Fr a b [vPOS,censusTotal]) := by
  refine ⟨resetState a,5,Ex.seq (Ex.op (OpEx.rstC a))
    (Ex.seq (Ex.op (OpEx.zero vPOS _)) (Ex.op (OpEx.zero censusTotal _))),le_rfl,?_⟩
  refine ⟨rfl,rfl,by simp [resetState],rfl,rfl,?_,?_⟩
  · refine ⟨?_,?_,?_,rfl⟩
    · simpa only [resetState,DS.set_env_ne _ _ (by decide : vZ≠censusTotal),
        DS.set_env_ne _ _ (by decide : vZ≠vPOS)] using hc.z
    · simpa only [resetState,DS.set_env_ne _ _ (by decide : v1≠censusTotal),
        DS.set_env_ne _ _ (by decide : v1≠vPOS)] using hc.one
    · simpa only [resetState,DS.set_env_ne _ _ (by decide : v2≠censusTotal),
        DS.set_env_ne _ _ (by decide : v2≠vPOS)] using hc.two
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hy
    rw [resetState,DS.set_env_ne _ _ hy.2,DS.set_env_ne _ _ hy.1]

end NearQuarticWires.StageCert.Incidence
