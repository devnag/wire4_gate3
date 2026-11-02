import Proof.Quartic.StagePrint.RawTargetCode
import Proof.Quartic.StagePrint.RawWeightEncoding

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces (intWord)
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: the strict target occupies the exact second load field. -/
def targetField (W : ℕ) (z : ℤ) : List Bool := weightField W (z-1)++[false]

/-- `lem:print`, paper/paper.tex: the target field has the same nested framing as the original-child input. -/
theorem targetField_eq (W : ℕ) (z : ℤ) :
    targetField W z=frame (frame (binary W (encS (z-1)))) := by
  rw [targetField,weightField_eq,←frame_eq_frameP]

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: the original threshold is read, changed to its exact strict target, and serialized with both framing layers. -/
def readTarget : St VV := .seq readInt (.seq encodeReady (.seq predecessorReady
  (.seq (emitBinary 2) (emitL [true,false,false]))))

/-- `lem:print`, paper/paper.tex: the original-target formatter touches only declared parser and field-writing registers. -/
def targetScratch : List (Fin VV) := readIntT ++ scratch

/-- `imp:disjoint`, `lem:print` and `prop:time`, paper/paper.tex: exact physical strictification and framing retain inclusive endpoint labels. -/
theorem readTarget_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (z : ℤ) (rest : List Bool) (W : ℕ)
    (hcw : C.cw.drop a.cp=intWord z++rest) (hwidth : a.env width=W)
    (hfit : encS z+3<2^C.Wd) (hW : W<2^C.Wd) (hctx : 3≤C.Wd)
    (hinput : C.cw.length+2≤C.Wd) (hlen : C.cw.length+2<2^C.Wd) :
    Hs C readTarget a (60*(intWord z).length+30*W+120) (fun b=>
      b.out=a.out++targetField W z ∧ b.cp=a.cp+(intWord z).length ∧
      b.wq=a.wq ∧ b.env width=W ∧ Cst b ∧ Fr a b targetScratch) := by
  unfold readTarget
  refine Hx.hs (Hs.then (readInt_spec a hc z rest hcw hinput hlen)
    (fun b ⟨bs,bv,_,bp,bw,bo,bc,bf⟩ n1 hn1=>?_))
  refine Hs.then (encodeReady_run C b bc z bv bs (by omega))
    (fun e ⟨ev,ep,ew,eo,ec,ef⟩ n2 hn2=>?_)
  have em : e.env t3=z.natAbs := by rw [ef t3 (by decide)];exact bv
  have es : e.env t8=if z<0 then 1 else 0 := by rw [ef t8 (by decide)];exact bs
  refine Hs.then (predecessorReady_run C e ec z em es ev hfit)
    (fun f ⟨fv,fp,fw,fo,fc,ff⟩ n3 hn3=>?_)
  have fwidth : f.env width=W := by
    rw [ff width (by decide),ef width (by decide),bf width (by decide)]
    exact hwidth
  refine Hs.then (emitBinary_run C 2 f fc _ W fv fwidth hW hctx)
    (fun g ⟨_,_,gwidth,go,gp,gw,gc,gf⟩ n4 hn4=>?_)
  refine Hs.last (emitL_spec (C:=C) [true,false,false] g)
    (fun j ⟨jo,jp,jw,jf⟩ n5 hn5=>?_)
  have jc : Cst j := Cst.of_fr gc jf (by decide)
    (by rw [jf vPOS (by decide),gc.pos,jp])
  refine ⟨⟨?_,jp.trans (gp.trans (fp.trans (ep.trans bp))),
    jw.trans (gw.trans (fw.trans (ew.trans bw))),?_,jc,?_⟩,?_⟩
  · rw [jo,go,fo,eo,bo]
    simp [targetField,weightField,List.append_assoc]
  · rw [jf width (by decide)];exact gwidth
  · exact (bf.weaken (by decide)).trans
      ((ef.weaken (by decide)).trans ((ff.weaken (by decide)).trans
      ((gf.weaken (by decide)).trans (jf.weaken (by decide)))))
  · norm_num at hn4 hn5
    omega

end NearQuarticWires.StagePrint.RawBits
