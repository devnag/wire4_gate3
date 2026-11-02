import Proof.Quartic.StagePrint.TranslationInit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.StagePrint.Header
open NearCubicGates.Close.Cells

/-- `imp:partition` and `lem:print`, paper/paper.tex: the actual r,b,s fields have distinct retained scalar slots. -/
def blockCount : Fin VV:=87
def blockWidth : Fin VV:=88
def syndromeWidth : Fin VV:=89

/-- `imp:partition` and `lem:print`, paper/paper.tex: the canonical block data are read from consecutive original parameter records. -/
def readHeaderGeometry : St VV MM :=
  .seq (.op (.copy index v2)) (.seq (.op (.inc index))
    (.seq (fetch StageLift.parameterStore index blockCount)
      (.seq (.op (.rdM StageLift.parameterStore syndromeWidth))
        (.op (.rdM StageLift.parameterStore blockWidth)))))

/-- `imp:partition` and `lem:print`, paper/paper.tex: the actual retained parameter bytes supply all block geometry, with the rewind and every field read paid. -/
theorem readHeaderGeometry_run (C : Ctx) (p : Cells.Parameters) (a : DS VV MM) (hc : Cst a)
    (hpar : a.ram StageLift.parameterStore=StageLift.parameterScalars p)
    (hcap : 4<2^C.Wd) :
    Hs C readHeaderGeometry a (a.rc StageLift.parameterStore+40) (fun b=>
      b.env blockCount=p.r ∧ b.env blockWidth=p.b ∧ b.env syndromeWidth=p.s ∧
      b.ip=a.ip ∧ b.out=a.out ∧ b.ram=a.ram ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b [index,c0,vJ,blockCount,syndromeWidth,blockWidth]) := by
  unfold readHeaderGeometry
  refine (Hs.seq (t2:=a.rc StageLift.parameterStore+34)
    (hs_copy C index v2 a (by decide)) ?_).mono (by omega) (fun _ h=>h)
  rintro b rfl
  let b:=a.set index (a.env v2)
  have bc : Cst b:=Cst.of_fr hc (show Fr a b [index] from Fr.set a _ (by simp)) (by decide)
  have bi : b.env index=2 := by simp [b,hc.two]
  refine (Hs.seq (t2:=a.rc StageLift.parameterStore+32)
    (hs_inc C index b (by rw [bi];omega)) ?_).mono (by omega) (fun _ h=>h)
  rintro d rfl
  let d:=b.set index (b.env index+1)
  have dc : Cst d:=Cst.of_fr bc (show Fr b d [index] from Fr.set b _ (by simp)) (by decide)
  have di : d.env index=3 := by simp [d,bi]
  have ef:=fetch_spec (C:=C) StageLift.parameterStore index blockCount (by decide) (by decide) d
    (by rw [di,show d.ram StageLift.parameterStore=StageLift.parameterScalars p from hpar,
      StageLift.parameterScalars_length];decide) (by rw [di];omega)
  rw [di] at ef
  refine (Hs.seq (t2:=3) ef ?_).mono (by simp [d,b]) (fun _ h=>h)
  rintro f ⟨fv,fi,fo,fr,fc,fkin,fkout,fkc,ff⟩
  have fp : f.ram StageLift.parameterStore=StageLift.parameterScalars p := by rw [fr];exact hpar
  have fcount : f.env blockCount=p.r := by
    rw [fv,show d.ram StageLift.parameterStore=StageLift.parameterScalars p from hpar]
    simp [StageLift.parameterScalars,StageLift.parameterHeadScalars]
  have fcur : f.rc StageLift.parameterStore=4 := by rw [fc];rfl
  refine Hs.seq (t2:=1) (hs_rdM C StageLift.parameterStore syndromeWidth f
    (by rw [fcur,fp,StageLift.parameterScalars_length];decide)) ?_
  rintro g rfl
  let g:=(f.set syndromeWidth ((f.ram StageLift.parameterStore).getD (f.rc StageLift.parameterStore) 0)).adv
    StageLift.parameterStore
  have gcur : g.rc StageLift.parameterStore=5 := by simp [g,DS.adv,fcur]
  refine (hs_rdM C StageLift.parameterStore blockWidth g
    (by rw [gcur,show g.ram StageLift.parameterStore=StageLift.parameterScalars p from fp,
      StageLift.parameterScalars_length];decide)).mono le_rfl ?_
  rintro out rfl
  have hfr : Fr a ((g.set blockWidth ((g.ram StageLift.parameterStore).getD
      (g.rc StageLift.parameterStore) 0)).adv StageLift.parameterStore)
      [index,c0,vJ,blockCount,syndromeWidth,blockWidth] := by
    intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hy
    have hy' : y∉[c0,vJ,blockCount] := by simp [hy.2.1,hy.2.2.1,hy.2.2.2.1]
    rw [show ((g.set blockWidth ((g.ram StageLift.parameterStore).getD
      (g.rc StageLift.parameterStore) 0)).adv StageLift.parameterStore).env y=f.env y by
        simp [g,DS.adv,DS.set,hy.2.2.2.2.1,hy.2.2.2.2.2]]
    rw [ff y hy']
    simp [d,b,DS.set,hy.1]
  refine ⟨?_,?_,?_,fi,fo,fr,Prod.ext fkin (Prod.ext fkout fkc),Cst.of_fr hc hfr (by decide),hfr⟩
  · simpa (config:={decide:=true}) [g,DS.adv,DS.set,syndromeWidth,blockCount,blockWidth] using fcount
  · change (g.ram StageLift.parameterStore).getD (g.rc StageLift.parameterStore) 0=p.b
    rw [gcur]
    change (f.ram StageLift.parameterStore).getD 5 0=p.b
    rw [fp]
    simp [StageLift.parameterScalars,StageLift.parameterHeadScalars]
  · simp (config:={decide:=true}) [g,DS.adv,DS.set,fcur,fp,StageLift.parameterScalars,
      StageLift.parameterHeadScalars,blockWidth,syndromeWidth]

end NearQuarticWires.StagePrint.Header
