import Proof.Quartic.StageCert.MomentSourceRead

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageMain.Compact

/-- `eq:testX`–`eq:testPhi` and `lem:print`, paper/paper.tex: population has one original cell
factor, while a moment has all eight original walk factors. -/
def momentFlagEdges {J : ℕ} : StageCertTests.TestOrdinal J→List (Fin 8)
  | .population => [0]
  | .digit _ _ _ | .finalError _ _ => List.ofFn fun edge : Fin 8=>edge

/-- `def:mask` and `lem:print`, paper/paper.tex: the actual tag selects precisely one or eight paid
structural source calls, in their literal mask-consumption order. -/
def emitMomentFlags : St VV MM :=
  .ite (.eq sourceTestTag vZ) (emitStructuralFlags [0])
    (emitStructuralFlags (List.ofFn fun edge : Fin 8=>edge))

/-- `def:mask`, `lem:print` and `prop:time`, paper/paper.tex: the physically parsed
test tag determines the exact original flag suffix for every witness;
neither a flag vector nor an incidence predicate is supplied. -/
theorem emitMomentFlags_run {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (width : ℕ) (input : List Bool) (L B K : ℕ)
    (hW : 2≤width) (hfit : (Program.prepWord B1 B2 r.call r.witness).length<2^width)
    (hNfit : 2*r.selected.1.N≤2^width)
    (hlfit : ∀edge,natBitLength (r.edgeRequest edge).left.val+2<2^width)
    (hrfit : ∀edge,natBitLength (r.edgeRequest edge).right.val+2<2^width)
    (hroom : ∀edge,(StageMainMask.structuralWord (r.edgeRequest edge)).length≤L)
    (hbudget : ∀edge,StageMainMask.structuralBudget (r.edgeRequest edge)≤B)
    (hcost : ∀edge,9*(Program.prepWord B1 B2 r.call r.witness).length+
      40*natBitLength (r.edgeRequest edge).left.val+
      40*natBitLength (r.edgeRequest edge).right.val+L+B+180≤K)
    (a : DS VV MM) (hc : Cst a) (hkin : a.kin=[])
    (hbits : a.ram compactStore=(Program.prepWord B1 B2 r.call r.witness).map Bool.toNat)
    (hlen : a.env compactLength=(Program.prepWord B1 B2 r.call r.witness).length)
    (hcursor : a.rc compactStore=(Program.prepWord B1 B2 r.call r.witness).length)
    (hb : a.env patternBase=r.selected.1.N) (hi : a.env sourceTermIndex=r.index.val)
    (htag : a.env sourceTestTag=(r.test.metadata r.selected.1).tag) :
    Hs (structuralSourceContext B1 B2 width input L B) emitMomentFlags a (8*(K+2)+2)
      (fun z=>z.out=a.out++structuralFlagList r (momentFlagEdges r.test) ∧
      z.ip=a.ip ∧ z.ram=a.ram ∧ z.rc=a.rc ∧ z.kin=[] ∧ Cst z ∧
      Fr a z (vJ::edgeStructuralScratch)) := by
  have hzero : (r.test.metadata r.selected.1).tag=0 ↔ r.test=.population := by
    cases r.test <;> simp [StageCertTests.TestOrdinal.metadata]
  unfold emitMomentFlags
  refine Hs.ite (t := 8*(K+2)+1) (c := .eq sourceTestTag vZ)
    (show sourceTestTag≠vZ by decide) ?_ ?_
  · intro he
    have ht : r.test=.population := hzero.mp (by
      simpa only [Cnd.eval,htag,hc.z,decide_eq_true_eq] using he)
    simpa only [ht,momentFlagEdges] using
      (emitStructuralFlags_run r [0] width input L B K hW hfit hNfit hlfit hrfit
        hroom hbudget hcost a hc hkin hbits hlen hcursor hb hi).mono
          (by change 1*(K+2)+1≤8*(K+2)+1; omega) (fun _ h=>h)
  · intro he
    have ht : r.test≠.population := fun h=>by
      have hh := hzero.mpr h
      simp only [Cnd.eval,htag,hc.z,hh,decide_true] at he
      cases he
    have hedges : momentFlagEdges r.test=List.ofFn (fun edge : Fin 8=>edge) := by
      cases htest : r.test with
      | population => exact False.elim (ht htest)
      | digit _ _ _ => rfl
      | finalError _ _ => rfl
    simpa only [hedges,List.length_ofFn] using
      (emitStructuralFlags_run r (List.ofFn fun edge : Fin 8=>edge) width input L B K
        hW hfit hNfit hlfit hrfit hroom hbudget hcost a hc hkin hbits hlen hcursor hb hi)

end NearQuarticWires.StageCert.Tokens
