import Proof.Quartic.StageCert.PopulationForm
import Proof.Quartic.StageCert.MomentExponent
import Proof.Quartic.StageCert.DigitMoment

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator
open NearQuarticWires.StageLift

/-- `eq:testX` and `lem:print`, paper/paper.tex: the complete original selected population moment
uses its actual structural source bit and physical exponent 2k. -/
def emitPopulationMoment (edge : Fin 8) : St VV MM :=
  .seq loadMaskParameters (.seq (.op (.rdI maskStructural))
    (.seq (StageLift.emitNaturalConstant maskStructural) (.seq preparePopulationExponent
      (.seq (emitPopulationForm witnessStore edge) (.seq (emitPower momentExponent)
        (StageLift.emitOperator .mul))))))

/-- `eq:testX`, `lem:print` and `prop:time`, paper/paper.tex: the full original
population moment is emitted from actual retained W2 records and
a literal structural-source bit, with all repeated labels retained. -/
theorem emitPopulationMoment_run (C : Ctx) (p : Cells.Parameters) (edge : Fin 8)
    (G Batom : ℕ) (bits : List Bool) (structural : Bool) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a) (hG : 1≤G) (hb : a.env atomCount=G)
    (hin : C.inp.drop a.ip=structural::rest)
    (hparams : a.ram parameterStore=parameterScalars p)
    (hwitness : a.ram witnessStore=bits.map Bool.toNat)
    (hRC : ∀m,a.rc m≤(a.ram m).length) (hKC : a.kc≤a.kout.length)
    (hbits : p.k+G≤bits.length) (haddress : p.k+G≤2^C.Wd)
    (hW : 5≤C.Wd) (hXfit : p.Xmax+1<2^C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀j,natBitLength (cornerRoleCode edge j*G+g)≤Batom)
    (hAtomFit : Batom+2<2^C.Wd) (hexp : 2*p.k<2^C.Wd)
    (hexpWord : natBitLength (2*p.k)+2<2^C.Wd) :
    Hs C (emitPopulationMoment edge) a
      (G*(bits.length+5*(p.k+G)+160*Batom+540)+40*natBitLength (2*p.k)+540) (fun z=>
      z.out=a.out++(toks (StagePrint.selectedPopulationMomentFormula (by decide : 0<4)
        (fun i : Fin G=>bits.getD (p.k+i.val) false) edge structural p.k)).flatMap tokWord ∧
      z.ip=a.ip+1 ∧ (z.ram,z.kin,z.kout,z.kc)=(a.ram,a.kin,a.kout,a.kc) ∧
      z.rc witnessStore≤bits.length ∧ Cst z ∧ Fr a z momentSourceScratch) := by
  have h32 : 32≤2^C.Wd := by
    have hh := Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide) hW
    norm_num at hh
    exact hh
  have hcur : a.rc parameterStore≤46 := by
    simpa only [hparams,parameterScalars_length] using hRC parameterStore
  have hpos : a.ip<C.inp.length := by
    by_contra h
    rw [List.drop_eq_nil_of_le (by omega)] at hin
    simp at hin
  have hread : bitOf C.inp a.ip=structural.toNat := by
    simpa using bitOf_drop (show C.inp.drop a.ip=[structural]++rest from hin) 0 (by change 0<1; omega)
  unfold emitPopulationMoment
  apply Hx.hs
  refine Hs.then ((loadMaskParameters_run C p a hc hparams hW hXfit).rc_le hRC hKC)
    (fun b ⟨⟨_,_,bk,_,bs,bc,bfr⟩,bRC,_⟩ n1 hn1=>?_)
  have bip : b.ip=a.ip := congrArg Prod.fst bs
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
  refine Hs.then (hs_rdI C maskStructural b (by rw [bip]; exact hpos))
    (fun d hd n2 hn2=>?_)
  subst hd
  let d : DS VV MM := { b.set maskStructural (bitOf C.inp b.ip) with ip:=b.ip+1 }
  have dfr : Fr b d [maskStructural] := Fr.set _ _ (by simp)
  have dc : Cst d := Cst.of_fr bc dfr (by decide)
  have dstruct : d.env maskStructural=structural.toNat := by
    change bitOf C.inp b.ip=structural.toNat
    rw [bip,hread]
  have hstruct : natBitLength (d.env maskStructural)≤1 := by
    rw [dstruct]
    cases structural <;> decide
  refine Hs.then ((StageLift.emitNaturalConstant_spec C maskStructural (by decide) (by decide)
    d dc (by omega) (by omega)).mono (t' := 96) (by omega) (fun _ h=>h))
    (fun e ⟨eo,es,ec,efr⟩ n3 hn3=>?_)
  have ek : e.env selectionStart=p.k :=
    (efr _ (by decide)).trans ((dfr _ (by decide)).trans bk)
  refine Hs.then (preparePopulationExponent_run C p.k e ec ek hexp)
    (fun f ⟨fexp,fs,fc,ffr⟩ n4 hn4=>?_)
  have af : Fr a f momentSourceScratch := (bfr.weaken (by decide)).trans
    ((dfr.weaken (by decide)).trans ((efr.weaken (by decide)).trans (ffr.weaken (by decide))))
  have fram : f.ram=a.ram := (congrArg (fun q=>q.2.2.1) fs).trans
    ((congrArg (fun q=>q.2.1) es).trans bram)
  have frc : f.rc=b.rc := (congrArg (fun q=>q.2.2.2.1) fs).trans
    (congrArg (fun q=>q.2.2.1) es)
  refine Hs.then (emitPopulationForm_run C witnessStore edge G p.k Batom bits f fc hG
    ((af _ (by decide)).trans hb) ((ffr _ (by decide)).trans ek)
    (by rw [fram]; exact hwitness)
    (by rw [frc]; simpa only [bram,hwitness,List.length_map] using bRC witnessStore)
    hbits haddress hW hindex hB hAtomFit)
    (fun q ⟨qo,qs,qr,qc,qfr⟩ n5 hn5=>?_)
  have qexp : q.env momentExponent=2*p.k := (qfr _ (by decide)).trans fexp
  refine Hs.then (emitPower_run C momentExponent (by decide) (by decide) q qc (by omega)
    (by rw [qexp]; exact hexpWord))
    (fun t ⟨to',ts,tc,tfr⟩ n6 hn6=>?_)
  refine Hs.last (StageLift.emitOperator_spec C .mul t tc)
    (fun z ⟨zo,zs,zc,zfr⟩ n7 hn7=>?_)
  have fo : f.out=e.out := congrArg (fun q=>q.2.1) fs
  have bo : b.out=a.out := congrArg (fun q=>q.2.1) bs
  have zr : z.rc=q.rc := (congrArg (fun q=>q.2.2.1) zs).trans (congrArg (fun q=>q.2.2.1) ts)
  refine ⟨⟨?_,?_,?_,by rw [zr]; exact qr,zc,
    af.trans ((qfr.weaken (by decide)).trans ((tfr.weaken (by decide)).trans (zfr.weaken (by decide))))⟩,?_⟩
  · rw [zo,to',qo,fo,eo,qexp,dstruct]
    change b.out++_++_++_++_=a.out++_
    rw [bo]
    cases structural <;> simp only [Bool.toNat_false,Bool.toNat_true,Nat.cast_zero,Nat.cast_one,
      StagePrint.selectedPopulationMomentFormula,toks,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.append_assoc,Bool.false_eq_true,if_false,if_true]
  · simp only [Prod.mk.injEq] at zs ts qs
    have fip : f.ip=b.ip+1 := (congrArg Prod.fst fs).trans (congrArg Prod.fst es)
    exact zs.1.trans (ts.1.trans (qs.1.trans (fip.trans (by omega))))
  · simp only [DS.sh,Prod.mk.injEq] at fs
    simp only [Prod.mk.injEq] at zs ts qs es ⊢
    exact ⟨zs.2.1.trans (ts.2.1.trans (qs.2.1.trans fram)),
      zs.2.2.2.1.trans (ts.2.2.2.1.trans (qs.2.2.1.trans (fs.2.2.2.2.1.trans (es.2.2.2.1.trans (congrArg (fun q=>q.2.2.2.2.1) bs))))),
      zs.2.2.2.2.1.trans (ts.2.2.2.2.1.trans (qs.2.2.2.1.trans (fs.2.2.2.2.2.1.trans (es.2.2.2.2.1.trans (congrArg (fun q=>q.2.2.2.2.2.1) bs))))),
      zs.2.2.2.2.2.trans (ts.2.2.2.2.2.trans (qs.2.2.2.2.trans (fs.2.2.2.2.2.2.trans (es.2.2.2.2.2.trans (congrArg (fun q=>q.2.2.2.2.2.2) bs)))))⟩
  · have hm : 2*(tokWord Tok.mul).length+1=15 := by decide
    rw [hm] at hn7
    rw [qexp] at hn6
    omega

end NearQuarticWires.StageCert.Tokens
