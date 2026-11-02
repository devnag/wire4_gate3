import Proof.Quartic.StageCert.FormulaTokens
import Proof.Quartic.Cells.Formulas

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `sec:cells` and `lem:print`(b,c), paper/paper.tex: the four literal atom indices are serialized in the exact
postfix order of the original integer mixed-residual formula. -/
def emitEdge (corners : Fin 4→Fin VV) : St VV MM :=
  .seq (emitAtom (corners 0)) (.seq (emitAtom (corners 1))
    (.seq (StageLift.emitOperator .sub) (.seq (emitAtom (corners 2))
      (.seq (StageLift.emitOperator .sub) (.seq (emitAtom (corners 3)) (StageLift.emitOperator .add))))))

/-- `sec:cells` and `lem:print`(b,c), paper/paper.tex: the actual emitter writes exactly the seven-token original
delta formula, preserving all coefficient stores and source metadata. -/
theorem emitEdge_run (C : Ctx) (corners : Fin 4→Fin VV) (V B : ℕ)
    (a : DS VV MM) (hc : Cst a) (hW : 2≤C.Wd)
    (hfree : ∀j,corners j∉StageLift.tokenScratch)
    (hB : ∀j,natBitLength (a.env (corners j))≤B) (hfit : B+2<2^C.Wd)
    (hV : ∀j,a.env (corners j)<V) :
    Hs C (emitEdge corners) a (160*B+260) (fun z =>
      z.out=a.out++(toks (Cells.deltaFormula (fun j=>⟨a.env (corners j),hV j⟩))).flatMap tokWord ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z StageLift.tokenScratch) := by
  have atom : ∀j r,Cst r→Fr a r StageLift.tokenScratch→
      Hs C (emitAtom (corners j)) r (40*B+50) (fun z=>
        z.out=r.out++tokWord (.var (a.env (corners j))) ∧
        (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(r.ip,r.ram,r.rc,r.kin,r.kout,r.kc) ∧
        Cst z ∧ Fr r z StageLift.tokenScratch) := by
    intro j r rc rf
    have hv : r.env (corners j)=a.env (corners j) := rf _ (hfree j)
    have h3 : corners j≠t3 := by intro h; exact hfree j (by simp [StageLift.tokenScratch,h])
    have hJ : corners j≠vJ := by intro h; exact hfree j (by simp [StageLift.tokenScratch,h])
    refine (emitAtom_run C (corners j) h3 hJ r rc hW
      (by rw [hv]; have hh := hB j; omega)).mono (by rw [hv]; have hh := hB j; omega) ?_
    intro z hz
    simpa only [hv] using hz
  unfold emitEdge
  apply Hx.hs
  refine Hs.then (atom 0 a hc (Fr.refl _ _))
    (fun b ⟨bo,br,bc,bf⟩ n1 hn1=>?_)
  refine Hs.then (atom 1 b bc bf)
    (fun d ⟨doo,dr,dc,df⟩ n2 hn2=>?_)
  refine Hs.then (StageLift.emitOperator_spec C .sub d dc)
    (fun e ⟨eo,er,ec,ef⟩ n3 hn3=>?_)
  have efr := bf.trans (df.trans (ef.weaken (by simp [StageLift.tokenScratch])))
  refine Hs.then (atom 2 e ec efr)
    (fun f ⟨fo,fr,fc,ff⟩ n4 hn4=>?_)
  refine Hs.then (StageLift.emitOperator_spec C .sub f fc)
    (fun g ⟨go,gr,gc,gf⟩ n5 hn5=>?_)
  have gfr := efr.trans (ff.trans (gf.weaken (by simp [StageLift.tokenScratch])))
  refine Hs.then (atom 3 g gc gfr)
    (fun h ⟨ho,hr,hc',hf⟩ n6 hn6=>?_)
  refine Hs.last (StageLift.emitOperator_spec C .add h hc')
    (fun z ⟨zo,zr,zc,zf⟩ n7 hn7=>?_)
  refine ⟨⟨?_,zr.trans (hr.trans (gr.trans (fr.trans (er.trans (dr.trans br))))),zc,
    gfr.trans (hf.trans (zf.weaken (by simp [StageLift.tokenScratch])))⟩,?_⟩
  · rw [zo,ho,go,fo,eo,doo,bo]
    simp only [Cells.deltaFormula,toks,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.append_assoc]
  · have hsub : 2*(tokWord Tok.sub).length+1=15 := by decide
    have hadd : 2*(tokWord Tok.add).length+1=11 := by decide
    rw [hsub] at hn3 hn5
    rw [hadd] at hn7
    omega

end NearQuarticWires.StageCert.Tokens
