import Proof.Gates.Cells.Kit

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: sum a fixed
list of actual binary registers using bounded binary additions. -/
def sumRegisters (target : Fin VV) : List (Fin VV)→St VV MM
  | []=>.op (.zero target)
  | source::sources=>.seq (sumRegisters target sources) (.op (.add target source))

/-- `prop:time`, paper/paper.tex: register sums
have a constant number of binary operations per real source field. -/
theorem sumRegisters_spec (C : Ctx) (target : Fin VV) (sources : List (Fin VV))
    (a : DS VV MM) (hne : target∉sources)
    (hfit : (sources.map a.env).sum<2^C.Wd) :
    Hs C (sumRegisters target sources) a (2*sources.length+1) (fun b=>
      b.env target=(sources.map a.env).sum ∧ b.sh=a.sh ∧ Fr a b [target]) := by
  induction sources with
  | nil =>
      refine (hs_zero C target a).mono (by simp) ?_
      rintro b rfl
      exact ⟨by simp,rfl,Fr.set a _ (by simp)⟩
  | cons source sources ih =>
      have htarget : target≠source := by intro h;exact hne (by simp [h])
      have htail : target∉sources := by intro h;exact hne (by simp [h])
      have htailfit : (sources.map a.env).sum<2^C.Wd := by
        simp only [List.map_cons,List.sum_cons] at hfit
        omega
      unfold sumRegisters
      refine (Hs.seq (t2:=1) (ih htail htailfit) fun b ⟨hb,hbsh,hbf⟩=>?_).mono
        (by simp only [List.length_cons];omega) (fun _ h=>h)
      have hsource : b.env source=a.env source := hbf source (by simp [htarget.symm])
      refine (hs_add C target source b htarget (by
        rw [hb,hsource]
        simp only [List.map_cons,List.sum_cons] at hfit
        omega)).mono le_rfl ?_
      rintro last rfl
      refine ⟨?_,hbsh,hbf.trans (Fr.set b _ (by simp))⟩
      simp only [DS.set_env_self,hb,hsource,List.map_cons,List.sum_cons]
      omega

/-- `prop:time`, paper/paper.tex: a squared
workspace hint is computed by one actual binary multiplication. -/
def squareRegister (source scratch target : Fin VV) : St VV MM :=
  .seq (.op (.copy scratch source)) (.op (.mul source scratch target))

/-- `prop:time`, paper/paper.tex: duplicating
the input and multiplying it establishes the exact square while
preserving all source streams and unrelated binary registers. -/
theorem squareRegister_spec (C : Ctx) (source scratch target : Fin VV)
    (hne : [source,scratch,target].Nodup) (a : DS VV MM)
    (hfit : a.env source^2<2^C.Wd) :
    Hs C (squareRegister source scratch target) a 3 (fun b=>
      b.env target=a.env source^2 ∧ b.sh=a.sh ∧ Fr a b [scratch,target]) := by
  have hss : source≠scratch := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
    exact hne.1.1
  have hst : source≠target := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
    exact hne.1.2
  have htt : scratch≠target := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
    exact hne.2.1
  unfold squareRegister
  refine Hs.seq (t2:=1) (hs_copy C scratch source a hss.symm) fun b hb=>?_
  subst b
  refine (hs_mul C source scratch target _ hss hst htt (by
    simp only [DS.set_env_self,DS.set_env_ne _ _ hss,pow_two] at hfit ⊢
    exact hfit)).mono le_rfl ?_
  rintro b rfl
  exact ⟨by simp only [DS.set_env_self,DS.set_env_ne _ _ hss,pow_two],rfl,
    (Fr.set a _ (by simp)).trans (Fr.set _ _ (by simp))⟩

end NearQuarticWires.StageFormulaMetadata
