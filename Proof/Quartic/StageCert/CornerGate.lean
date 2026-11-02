import Proof.Quartic.StageMain.Gate
import Proof.Quartic.StageCert.StructuralBuilder

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain

/-- `sec:cells`, paper/paper.tex: the packed original
points are ordered as `c`, `c xor u`, `c xor v`, `c xor u xor v`. -/
def cornerPoint (l : Fin 4) : Fin VV := ⟨114+l.val,by change 114+l.val<256; have := l.isLt; omega⟩

/-- `sec:cells`, paper/paper.tex: one raw threshold result
is retained for each of the four original cell points. -/
def cornerBit (l : Fin 4) : Fin VV := ⟨128+l.val,by change 128+l.val<256; have := l.isLt; omega⟩

/-- `sec:cells`, paper/paper.tex: one corner evaluation
reads the complete original raw gate word at the current source cursor. -/
def scoreCorner (l : Fin 4) : St VV :=
  .seq (.op (.copy pointSaved (cornerPoint l)))
    (.seq scoreGate (.op (.copy (cornerBit l) gateResult)))

/-- `sec:cells`, paper/paper.tex: one corner evaluator
changes only the selected gate bit and the concrete raw-gate workspace. -/
def scoreCornerScratch (l : Fin 4) : List (Fin VV) :=
  pointSaved::cornerBit l::scoreGateScratch

/-- `sec:cells` and `prop:time`, paper/paper.tex: evaluating a corner is a paid original-source computation,
including inclusive threshold ties and arbitrary signed gate weights. -/
theorem scoreCorner_run (C : Ctx) {n : ℕ} (g : NormalizedThresholdGate n)
    (l : Fin 4) (a : DS VV) (hc : Cst a) (rest : List Bool)
    (hin : C.cw.drop a.cp=gateWord g++rest)
    (hW : C.cw.length+3≤C.Wd) (hpoint : a.env (cornerPoint l)<2^C.Wd) :
    Hs C (scoreCorner l) a (200*(C.cw.length+2)^2+4) (fun z =>
      z.env (cornerBit l)=(g.eval (packedPoint n (a.env (cornerPoint l)))).toNat ∧
      z.cp=a.cp+(gateWord g).length ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧
      FrS a z (scoreCornerScratch l)) := by
  unfold scoreCorner
  apply Hx.hs
  refine Hs.then (hs_copy C pointSaved (cornerPoint l) a (by fin_cases l <;> decide))
    (fun r hr n1 hn1 => ?_)
  subst hr
  have rc : Cst (a.set pointSaved (a.env (cornerPoint l))) :=
    Cst.of_fr hc (Fr.set (T := [pointSaved]) _ _ (by simp)) (by decide)
      (by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos)
  refine Hs.then (scoreGate_spec g _ rc rest (by exact hin) hW
    (by rw [DS.set_env_self]; exact hpoint))
    (fun s ⟨sg,scp,sw,so,sconst,sfr⟩ n2 hn2 => ?_)
  refine Hs.last (hs_copy C (cornerBit l) gateResult s (by fin_cases l <;> decide))
    (fun z hz n3 hn3 => ?_)
  subst hz
  refine ⟨⟨by simpa only [DS.set_env_self] using sg,scp,sw,so,?_,?_⟩,?_⟩
  · exact Cst.of_fr sconst (Fr.set (T := [cornerBit l]) _ _ (by simp))
      (by fin_cases l <;> decide)
      (by rw [DS.set_env_ne _ _ (by fin_cases l <;> decide)]; exact sconst.pos)
  · exact ((Fr.set (T := [pointSaved]) _ _ (by simp)).toS.weaken
      (by simp [scoreCornerScratch])).trans
      ((sfr.weaken (by intro y hy; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))).trans
        ((Fr.set (T := [cornerBit l]) _ _ (by simp)).toS.weaken (by simp [scoreCornerScratch])))
  · omega

end NearQuarticWires.StageCert
