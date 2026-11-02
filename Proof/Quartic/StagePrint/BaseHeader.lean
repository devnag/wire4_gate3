import Proof.Quartic.StagePrint.HeaderSource
import Proof.Quartic.StagePrint.HeaderWidthProgram
import Proof.Quartic.StagePrint.HeaderGeometry
import Proof.Quartic.StagePrint.SourceValidity

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `imp:partition`, `imp:pullback` and `lem:print`, paper/paper.tex: all walk-independent affine header values are physically computed from the retained original source. -/
def baseHeaderProgram : St VV MM := .seq readTranslation
  (.seq readCallArity (.seq headerWidthProgram readHeaderGeometry))

/-- `prop:time`, paper/paper.tex: every actual memory rewind, binary-prefix loop and width calculation is included. -/
def baseHeaderCost (c : Call) (p : Cells.Parameters) (w : List Bool) : ℕ :=
  (106+translationCost (Program.witnessPrefix c p w).length p.k)+1+
    ((callWord c).length+30*natBitLength c.n+40+1+(5*Nat.size c.n+109+1+86))

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the actual original call and witness determine the first seven scalar header fields, independently of the current child and walk role. -/
structure BaseHeaderData (request : HeaderCall) (a : DS VV MM) : Prop where
  n : a.env arity=request.call.n
  sourceWidth : a.env Lin=(4*request.call.n+1)*Nat.clog 2 (request.call.n+1)+5
  targetWidth : a.env Lout=(4*request.call.n+1)*Nat.clog 2 (request.call.n+1)+5+request.call.n+6
  r : a.env blockCount=request.parameters.r
  b : a.env blockWidth=request.parameters.b
  s : a.env syndromeWidth=request.parameters.s
  translation : a.env translation=StagePullback.translationNumber
    (Builder.star request.call request.prepared)
    (Builder.translation request.call request.prepared request.witness)

/-- `imp:partition`, `imp:pullback` and `lem:print`, paper/paper.tex: the complete fixed header prefix is computed by actual source operations, with no supplied dimension, width, geometry or syndrome number. -/
theorem baseHeaderProgram_run (C : Ctx) (req : HeaderCall)
    (a : DS VV MM) (hc : Cst a) (ha : Valid C a) (hd : HeaderSourceData req a)
    (hWd : req.call.n+3≤C.Wd)
    (hcap : 4*(req.call.n+1)^2+req.call.n+20<2^C.Wd) :
    Hs C baseHeaderProgram a (baseHeaderCost req.call req.parameters req.witness)
      (fun b=>BaseHeaderData req b ∧ b.ram=a.ram ∧ b.ip=a.ip ∧ b.out=a.out ∧
        (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧ Valid C b) := by
  let c:=req.call
  have hWdc : c.n+3≤C.Wd := hWd
  let p:=req.parameters
  let w:=req.witness
  let A:=(callWord c).length+30*natBitLength c.n+40
  let W:=5*Nat.size c.n+109
  unfold baseHeaderProgram baseHeaderCost
  refine (Hs.seq (t2:=A+1+(W+1+86)) (source_addValid (by omega) ha (readHeaderTranslation_run C req a hc ha hd hWd)) ?_).mono (by dsimp [A,W,c,p,w];omega) (fun _ h=>h)
  rintro b ⟨⟨bt,br,bi,bo,bs,bc⟩,bv⟩
  have bcall : b.ram StageLift.callStore=(callWord c).map Bool.toNat := by rw [br];exact hd.originalCall
  have barg:=source_addValid (by omega) bv (readCallArity_run C c b bc bcall (by
    have hh : natBitLength c.n≤c.n+1 := by
      unfold natBitLength
      have h1:=Nat.log_lt_self 2 (show c.n+1≠0 by omega)
      have h2:=Nat.log_mono_right (show c.n≤c.n+1 by omega) (b:=2)
      omega
    omega))
  have bcursor : b.rc StageLift.callStore≤(callWord c).length := by
    have hh:=bv.rc_le StageLift.callStore
    simpa [bcall] using hh
  refine (Hs.seq (t2:=W+1+86) (barg.mono (show b.rc StageLift.callStore+30*natBitLength c.n+40≤
    (callWord c).length+30*natBitLength c.n+40 by omega) (fun _ h=>h)) ?_).mono (by dsimp [A];omega) (fun _ h=>h)
  rintro d ⟨⟨dn,di,do_,dr,ds,dc,dfr⟩,dv⟩
  refine (Hs.seq (t2:=86) (source_addValid (by omega) dv
    (headerWidthProgram_run C d dc c.n dn hcap)) ?_).mono (by dsimp [W];omega) (fun _ h=>h)
  rintro e ⟨⟨el,eo,esh,ec,efr⟩,ev⟩
  have er : e.ram=d.ram:=congrArg (fun t=>t.2.2.1) esh
  have ep : e.ram StageLift.parameterStore=StageLift.parameterScalars p := by
    rw [er,dr,br]
    exact hd.scalarFields
  have ecursor : e.rc StageLift.parameterStore≤46 := by
    have hh:=ev.rc_le StageLift.parameterStore
    simpa [ep,StageLift.parameterScalars_length] using hh
  have eg:=source_addValid (by omega) ev (readHeaderGeometry_run C p e ec ep (by omega))
  refine eg.mono (by omega) ?_
  rintro f ⟨⟨fr,fb,fs,fi,fo,fmem,fstreams,fc,ff⟩,fv⟩
  have fn : f.env arity=c.n := by rw [ff arity (by decide),efr arity (by decide)];exact dn
  have fl : f.env Lin=(4*c.n+1)*Nat.clog 2 (c.n+1)+5 := by rw [ff Lin (by decide)];exact el
  have fout : f.env Lout=(4*c.n+1)*Nat.clog 2 (c.n+1)+5+c.n+6 := by rw [ff Lout (by decide)];exact eo
  have ft : f.env translation=b.env translation := by
    rw [ff translation (by decide),efr translation (by decide),dfr translation (by decide)]
  have ei : e.ip=d.ip:=congrArg (fun t=>t.1) esh
  have eout : e.out=d.out:=congrArg (fun t=>t.2.1) esh
  have estr : (e.kin,e.kout,e.kc)=(d.kin,d.kout,d.kc) :=
    congrArg (fun t=>(t.2.2.2.2.1,t.2.2.2.2.2.1,t.2.2.2.2.2.2)) esh
  refine ⟨⟨fn,fl,fout,fr,fb,fs,ft.trans bt⟩,fmem.trans (er.trans (dr.trans br)),
    fi.trans (ei.trans (di.trans bi)),fo.trans (eout.trans (do_.trans bo)),
    fstreams.trans (estr.trans (ds.trans bs)),fc,fv⟩

end NearQuarticWires.StagePrint.Header
