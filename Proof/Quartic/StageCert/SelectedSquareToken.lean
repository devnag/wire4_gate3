import Proof.Quartic.StageCert.OriginalEdgeTokens
import Proof.Quartic.StagePrint.SelectedFormulas

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `def:mask` and `lem:print`(c), paper/paper.tex: the actual retained selection bit for the current original
occurrence is retained during its complete quadratic token emission. -/
def selectedTokenBit : Fin VV := ⟨105,by decide⟩

/-- `def:mask` and `lem:print`(c), paper/paper.tex: a witness-selected quadratic residual has the literal
zero branch or its original four-corner edge followed by exponent two. -/
def emitSelectedSquare (edge : Fin 8) : St VV MM :=
  .ite (.eq selectedTokenBit vZ) (StageLift.emitOperator (.const 0))
    (.seq (emitOriginalEdge edge) (StageLift.emitOperator (.pow 2)))

/-- `lem:print`(c), paper/paper.tex: selected
quadratic tokens are emitted exactly on the original seventeen-role pool,
without assuming a population or a passing certificate. -/
theorem emitSelectedSquare_run (C : Ctx) (edge : Fin 8) (G g B : ℕ)
    (selection : Fin G→Bool) (hgG : g<G) (a : DS VV MM) (hc : Cst a)
    (hG : a.env atomCount=G) (hg : a.env atomOccurrence=g)
    (hs : a.env selectedTokenBit=(selection ⟨g,hgG⟩).toNat)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hfit : B+2<2^C.Wd) :
    Hs C (emitSelectedSquare edge) a (160*B+500) (fun z=>
      z.out=a.out++(toks (StagePrint.selectedSquare (by decide : 0<4)
        selection edge ⟨g,hgG⟩)).flatMap tokWord ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z (atomRole::atomValue::StageLift.tokenScratch)) := by
  unfold emitSelectedSquare
  refine Hs.ite (t := 160*B+499) (c := .eq selectedTokenBit vZ)
    (show selectedTokenBit≠vZ by decide) ?_ ?_
  · intro he
    have hz : selection ⟨g,hgG⟩=false := by
      simpa only [Cnd.eval,hs,hc.z,decide_eq_true_eq,Bool.toNat_eq_zero] using he
    refine (StageLift.emitOperator_spec C (.const 0) a hc).mono
      (by
        have hl : (tokWord (.const 0)).length=9 := by decide
        rw [hl]
        omega) ?_
    rintro z ⟨zo,zr,zc,zfr⟩
    exact ⟨by simpa [StagePrint.selectedSquare,hz,toks] using zo,zr,zc,
      zfr.weaken (by simp [StageLift.tokenScratch])⟩
  · intro he
    have hz : selection ⟨g,hgG⟩=true := by
      cases hb : selection ⟨g,hgG⟩ with
      | false => simp [Cnd.eval,hs,hc.z,hb] at he
      | true => rfl
    refine (Hs.seq (t1 := 160*B+440) (t2 := 25)
      (emitOriginalEdge_run C edge G g B a hc hG hg hgG hW hindex hB hfit) ?_).mono
        (by omega) (fun _ h=>h)
    rintro b ⟨bo,br,bc,bfr⟩
    refine (StageLift.emitOperator_spec C (.pow 2) b bc).mono (by decide) ?_
    rintro z ⟨zo,zr,zc,zfr⟩
    refine ⟨?_,zr.trans br,zc,bfr.trans (zfr.weaken (by simp [StageLift.tokenScratch]))⟩
    rw [zo,bo]
    simp [StagePrint.selectedSquare,hz,toks,List.flatMap_append,List.append_assoc]

end NearQuarticWires.StageCert.Tokens
