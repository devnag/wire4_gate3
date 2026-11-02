import Proof.Quartic.StageCert.OriginalAtomToken
import Proof.Quartic.Cells.WalkFormulas

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `lem:print`(b,c), paper/paper.tex: a concrete edge
formula computes every original-pool atom index before serializing its token. -/
def emitOriginalEdge (edge : Fin 8) : St VV MM :=
  .seq (emitOriginalAtom (cornerRoleCode edge 0))
    (.seq (emitOriginalAtom (cornerRoleCode edge 1))
      (.seq (StageLift.emitOperator .sub)
        (.seq (emitOriginalAtom (cornerRoleCode edge 2))
          (.seq (StageLift.emitOperator .sub)
            (.seq (emitOriginalAtom (cornerRoleCode edge 3)) (StageLift.emitOperator .add))))))

/-- `lem:print`(b,c), paper/paper.tex: the physical
postfix stream equals the literal edge formula on the unchanged original
seventeen-role occurrence pool, with all source fields and stores retained. -/
theorem emitOriginalEdge_run (C : Ctx) (edge : Fin 8) (G g B : ℕ)
    (a : DS VV MM) (hc : Cst a) (hG : a.env atomCount=G) (hg : a.env atomOccurrence=g)
    (hgG : g<G) (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hfit : B+2<2^C.Wd) :
    Hs C (emitOriginalEdge edge) a (160*B+440) (fun z=>
      z.out=a.out++(toks (Cells.edgeFormula (by decide : 0<4) edge ⟨g,hgG⟩)).flatMap tokWord ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z (atomRole::atomValue::StageLift.tokenScratch)) := by
  let T := atomRole::atomValue::StageLift.tokenScratch
  have hr : ∀j,cornerRoleCode edge j<17 := by
    intro j
    rw [←cornerRoleCode_eq]
    exact (Cells.offsetIndex 4 (Cells.cornerRole (by decide : 0<4) edge j)).isLt
  have hp : 32≤2^C.Wd := by
    have h := Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide) hW
    norm_num at h
    exact h
  have atom : ∀j r,Cst r→Fr a r T→
      Hs C (emitOriginalAtom (cornerRoleCode edge j)) r (40*B+92) (fun z=>
        z.out=r.out++tokWord (.var (cornerRoleCode edge j*G+g)) ∧
        (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(r.ip,r.ram,r.rc,r.kin,r.kout,r.kc) ∧
        Cst z ∧ Fr r z T) := by
    intro j r rc rf
    have rG : r.env atomCount=G := (rf _ (by decide)).trans hG
    have rg : r.env atomOccurrence=g := (rf _ (by decide)).trans hg
    have hrole := hr j
    have hval : cornerRoleCode edge j*G+g<17*G := by nlinarith
    exact (emitOriginalAtom_run C (cornerRoleCode edge j) G g r rc rG rg (by omega)
      (by omega) (hval.trans hindex) (by have hh := hB j; omega)).mono
        (by have hh := hB j; omega) (fun _ h=>h)
  unfold emitOriginalEdge
  apply Hx.hs
  refine Hs.then (atom 0 a hc (Fr.refl _ _)) (fun b ⟨bo,br,bc,bf⟩ n1 hn1=>?_)
  refine Hs.then (atom 1 b bc bf) (fun d ⟨doo,dr,dc,df⟩ n2 hn2=>?_)
  refine Hs.then (StageLift.emitOperator_spec C .sub d dc) (fun e ⟨eo,er,ec,ef⟩ n3 hn3=>?_)
  have efr := bf.trans (df.trans (ef.weaken (by simp [T,StageLift.tokenScratch])))
  refine Hs.then (atom 2 e ec efr) (fun f ⟨fo,fr,fc,ff⟩ n4 hn4=>?_)
  refine Hs.then (StageLift.emitOperator_spec C .sub f fc) (fun h ⟨ho,hr',hc',hf⟩ n5 hn5=>?_)
  have hfr := efr.trans (ff.trans (hf.weaken (by simp [T,StageLift.tokenScratch])))
  refine Hs.then (atom 3 h hc' hfr) (fun q ⟨qo,qr,qc,qf⟩ n6 hn6=>?_)
  refine Hs.last (StageLift.emitOperator_spec C .add q qc) (fun z ⟨zo,zr,zc,zf⟩ n7 hn7=>?_)
  refine ⟨⟨?_,zr.trans (qr.trans (hr'.trans (fr.trans (er.trans (dr.trans br))))),zc,
    hfr.trans (qf.trans (zf.weaken (by simp [T,StageLift.tokenScratch])))⟩,?_⟩
  · rw [zo,qo,ho,fo,eo,doo,bo]
    simp only [Cells.edgeFormula,Cells.deltaFormula,toks,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.append_assoc,atomIndex_eq_code]
  · have hs : 2*(tokWord Tok.sub).length+1=15 := by decide
    have ha : 2*(tokWord Tok.add).length+1=11 := by decide
    rw [hs] at hn3 hn5
    rw [ha] at hn7
    omega

end NearQuarticWires.StageCert.Tokens
