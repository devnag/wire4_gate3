import Proof.Quartic.StagePrint.TranslationLoop
import Proof.Quartic.StageLift.ParameterReader
import Proof.Quartic.StageLift.PrintFrames

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `sec:params`, witness (W1) and `lem:print`, paper/paper.tex: the actual k field is fetched from the retained scalar record before the translation accumulator is initialized. -/
def readTranslation : St VV MM :=
  .seq (.op (.copy index v2))
    (.seq (.op (.add index v2))
      (.seq (.op (.add index v2))
        (.seq (fetch StageLift.parameterStore index count)
          (.seq (.op (.zero translation))
            (.seq (.op (.copy power v1)) (translationLoop StageLift.witnessStore))))))

/-- `sec:params`, witness (W1) and `lem:print`, paper/paper.tex: no preinitialized length, syndrome number or accumulator is supplied to the translation producer. -/
theorem readTranslation_run (C : Ctx) (p : Cells.Parameters) (bits : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hpar : a.ram StageLift.parameterStore=StageLift.parameterScalars p)
    (hwit : a.ram StageLift.witnessStore=bits.map Bool.toNat)
    (hbits : p.k≤bits.length) (hcap : 2^p.k<2^C.Wd) (hsmall : 7<2^C.Wd) :
    Hs C readTranslation a
      (a.rc StageLift.parameterStore+60+translationCost (a.rc StageLift.witnessStore) p.k)
      (fun b=>b.env translation=binaryPrefix bits p.k ∧ b.ram=a.ram ∧
        b.ip=a.ip ∧ b.out=a.out ∧ (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b) := by
  let L:=translationCost (a.rc StageLift.witnessStore) p.k
  unfold readTranslation
  refine (Hs.seq (t2:=a.rc StageLift.parameterStore+48+L) (hs_copy C index v2 a (by decide)) ?_).mono (by omega) (fun _ h=>h)
  rintro b rfl
  let b:=a.set index (a.env v2)
  have bc : Cst b:=Cst.of_fr hc (show Fr a b [index] from Fr.set a _ (by simp)) (by decide)
  have bi : b.env index=2 := by simp [b,hc.two]
  refine (Hs.seq (t2:=a.rc StageLift.parameterStore+46+L) (hs_add C index v2 b (by decide) (by simp [bi,bc.two];omega)) ?_).mono (by omega) (fun _ h=>h)
  rintro d rfl
  let d:=b.set index (b.env index+b.env v2)
  have dc : Cst d:=Cst.of_fr bc (show Fr b d [index] from Fr.set b _ (by simp)) (by decide)
  have di : d.env index=4 := by simp [d,bi,bc.two]
  refine (Hs.seq (t2:=a.rc StageLift.parameterStore+44+L) (hs_add C index v2 d (by decide) (by simp [di,dc.two];omega)) ?_).mono (by omega) (fun _ h=>h)
  rintro e rfl
  let e:=d.set index (d.env index+d.env v2)
  have ec : Cst e:=Cst.of_fr dc (show Fr d e [index] from Fr.set d _ (by simp)) (by decide)
  have ei : e.env index=6 := by simp [e,di,dc.two]
  have eg : e.ram StageLift.parameterStore=StageLift.parameterScalars p := hpar
  have ef:=fetch_spec (C:=C) StageLift.parameterStore index count (by decide) (by decide) e
    (by rw [ei,eg,StageLift.parameterScalars_length];decide) (by rw [ei];omega)
  rw [ei] at ef
  refine (Hs.seq (t2:=4+L) ef ?_).mono (by simp [e,d,b];omega) (fun _ h=>h)
  rintro f ⟨fv,fi,fo,fr,fcursor,fkin,fkout,fkc,ff⟩
  have fconst : Cst f:=Cst.of_fr ec ff (by decide)
  have fk : f.env count=p.k := by
    rw [fv,eg]
    simp [StageLift.parameterScalars,StageLift.parameterHeadScalars]
  refine (Hs.seq (t2:=2+L) (hs_zero C translation f) ?_).mono (by omega) (fun _ h=>h)
  rintro g rfl
  let g:=f.set translation 0
  have gc : Cst g:=Cst.of_fr fconst (show Fr f g [translation] from Fr.set f _ (by simp)) (by decide)
  refine (Hs.seq (t2:=L) (hs_copy C power v1 g (by decide)) ?_).mono (by omega) (fun _ h=>h)
  rintro h rfl
  let h:=g.set power (g.env v1)
  have hh : Cst h:=Cst.of_fr gc (show Fr g h [power] from Fr.set g _ (by simp)) (by decide)
  have hk : h.env count=p.k := by simpa (config:={decide:=true}) [h,g,power,translation,count] using fk
  have eh:=translationLoop_run C StageLift.witnessStore bits p.k h hh
    (by simpa [h,g,fr,e,d,b] using hwit) hbits hk
    (by simp (config:={decide:=true}) [h,g,power,translation])
    (by simp [h,gc.one]) hcap
  have hfcur : h.rc StageLift.witnessStore=a.rc StageLift.witnessStore := by
    change f.rc StageLift.witnessStore=_
    rw [fcursor]
    simp [StageLift.parameterStore,StageLift.witnessStore,e,d,b]
  rw [hfcur] at eh
  refine eh.mono le_rfl ?_
  rintro out ⟨ov,_op,oi,oo,orr,os,oc,_ofr⟩
  exact ⟨ov,orr.trans fr,oi.trans fi,oo.trans fo,os.trans (Prod.ext fkin (Prod.ext fkout fkc)),oc⟩

end NearQuarticWires.StagePrint.Header
