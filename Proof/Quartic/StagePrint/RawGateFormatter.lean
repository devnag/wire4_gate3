import Proof.Quartic.StagePrint.RawGateWeights
import Proof.Quartic.StagePrint.RawTargetField
import Proof.Quartic.StagePrint.RawUnary
import Proof.Quartic.StagePrint.RawZeroFields
import Proof.Quartic.StagePrint.OriginalChildMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces (intWord listWord)
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine (Top.loadRec)

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: the original gate's physical child-compiler input is constructed before any corner offset is applied. -/
def formatOriginalGate : St VV := .seq readGateWeights (.seq readTarget
  (.seq (emitConstantField 2) (.seq (emitConstantField 0)
    (.seq emitUnaryField (zeroFields 6)))))

/-- `lem:print`, paper/paper.tex: all parser and formatting scratch registers are declared explicitly. -/
def gateFormatterScratch : List (Fin VV) := gateWeightsScratch ++ targetScratch

/-- `prop:time`, paper/paper.tex: the source-to-original-child record conversion has an explicit polynomial cost in the dense source and word sizes. -/
def gateFormatterCost (C : Ctx) (r : OriginalChildRequest) : ℕ :=
  100*(C.cw.length+2)+(r.weights.length+1)*(60*C.cw.length+30*(r.W+1)+130)+
  60*(intWord (r.target+1)).length+300*(r.W+1)+9*r.weights.length+300

/-- `imp:disjoint`, `lem:print` and `prop:time`, paper/paper.tex: the complete original gate word is physically converted to the exact cold child-compiler record, preserving every original weight and inclusive threshold label. -/
theorem formatOriginalGate_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (r : OriginalChildRequest) (rest : List Bool)
    (hcw : C.cw.drop a.cp=listWord intWord r.weights++intWord (r.target+1)++rest)
    (hwidth : a.env width=r.W+1)
    (hfit : ∀z∈r.weights,encS z<2^C.Wd)
    (htarget : encS (r.target+1)+3<2^C.Wd)
    (hW : r.W+1<2^C.Wd) (hcount : r.weights.length<2^C.Wd)
    (hctx : 3≤C.Wd) (hinput : C.cw.length+2≤C.Wd)
    (hlen : C.cw.length+2<2^C.Wd) :
    Hs C formatOriginalGate a (gateFormatterCost C r) (fun b=>
      b.out=a.out++r.word ∧
      b.cp=a.cp+(listWord intWord r.weights++intWord (r.target+1)).length ∧
      b.wq=a.wq ∧ b.env width=r.W+1 ∧ Cst b ∧ Fr a b gateFormatterScratch) := by
  unfold formatOriginalGate
  refine Hx.hs (Hs.then (readGateWeights_run C a hc r.weights _ (r.W+1)
    (by simpa only [List.append_assoc] using hcw) hwidth hfit hW hcount hctx hinput hlen)
    (fun b ⟨bo,bp,bw,bwidth,bn,bc,bf⟩ n1 hn1=>?_))
  have bd : C.cw.drop b.cp=intWord (r.target+1)++rest := by
    rw [bp,←List.drop_drop,hcw,List.append_assoc,List.drop_left]
  refine Hs.then (readTarget_run C b bc (r.target+1) rest (r.W+1)
    bd bwidth htarget hW hctx hinput hlen)
    (fun e ⟨eo,ep,ew,ewidth,ec,ef⟩ n2 hn2=>?_)
  refine Hs.then (emitConstantField_run C e ec 2 (r.W+1) ewidth
    (by have : 8≤2^C.Wd:=(by norm_num :8≤2^3).trans
          (Nat.pow_le_pow_right (by decide) hctx);omega) hW hctx)
    (fun f ⟨fo,fp,fw,fwidth,fc,ff⟩ n3 hn3=>?_)
  refine Hs.then (emitConstantField_run C f fc 0 (r.W+1) fwidth
    (by positivity) hW hctx)
    (fun g ⟨go,gp,gw,gwidth,gc,gf⟩ n4 hn4=>?_)
  have gn : g.env weightCount=r.weights.length := by
    rw [gf weightCount (by decide),ff weightCount (by decide),ef weightCount (by decide)]
    exact bn
  refine Hs.then (emitUnaryField_run C g gc r.weights.length gn hcount)
    (fun j ⟨jo,jp,jw,jc,jf⟩ n5 hn5=>?_)
  have jwidth : j.env width=r.W+1 := by rw [jf width (by decide)];exact gwidth
  refine Hs.last (zeroFields_run C (r.W+1) hW hctx 6 j jc jwidth)
    (fun k ⟨ko,kp,kw,kwidth,kc,kf⟩ n6 hn6=>?_)
  refine ⟨⟨?_,?_,kw.trans (jw.trans (gw.trans (fw.trans (ew.trans bw)))),kwidth,kc,?_⟩,?_⟩
  · rw [ko,jo,go,fo,eo,bo]
    have ht : r.target+1-1=r.target := by omega
    simp only [targetField_eq,ht,OriginalChildRequest.word,Top.loadRec,
      List.replicate_succ,List.replicate_zero,List.flatten_cons,List.flatten_nil,List.append_nil]
    simp only [List.append_assoc]
  · rw [kp,jp,gp,fp,ep,bp,List.length_append]
    omega
  · exact (bf.weaken (by decide)).trans ((ef.weaken (by decide)).trans
      ((ff.weaken (by decide)).trans ((gf.weaken (by decide)).trans
      ((jf.weaken (by decide)).trans (kf.weaken (by decide))))))
  · unfold gateFormatterCost
    omega

end NearQuarticWires.StagePrint.RawBits
