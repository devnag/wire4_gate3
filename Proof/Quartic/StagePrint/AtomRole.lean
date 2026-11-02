import Proof.Quartic.StagePrint.RoleDispatch

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Header
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: actual occurrence count, parsed polynomial atom, and selected ORIGINAL occurrence are distinct physical scalar fields. -/
def occurrenceCount : Fin VV:=96
def atomValue : Fin VV:=116
def originalIndex : Fin VV:=104

/-- `lem:print`, paper/paper.tex: one actual division separates the offset role from the original occurrence index before sharp decomposition. -/
def splitAtom : St VV MM:=.op (.dm atomValue occurrenceCount roleIndex originalIndex)

/-- `lem:print`, paper/paper.tex: the runtime quotient and remainder are the literal canonical product-index components of the parsed formula variable. -/
theorem splitAtom_run (C : Ctx) (G : ℕ) (i : Fin (17*G)) (a : DS VV MM)
    (hi : a.env atomValue=i.val) (hG : a.env occurrenceCount=G)
    (hpos : 0<G) (hfit : 2*G≤2^C.Wd) :
    Hs C splitAtom a 1 (fun b=>
      b.env roleIndex=(finProdFinEquiv.symm i).1.val ∧
      b.env originalIndex=(finProdFinEquiv.symm i).2.val ∧
      b.sh=a.sh ∧ Fr a b [roleIndex,originalIndex]) := by
  unfold splitAtom
  refine (hs_dm C atomValue occurrenceCount roleIndex originalIndex a
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hG];exact hpos) (by rw [hG];exact hfit)).mono le_rfl ?_
  rintro b rfl
  refine ⟨?_,?_,rfl,(Fr.set a _ (by simp)).trans (Fr.set _ _ (by simp))⟩
  · simp only [DS.set_env_ne _ _ (by decide : roleIndex≠originalIndex),DS.set_env_self,hi,hG]
    rfl
  · simp only [DS.set_env_self,hi,hG]
    rfl

/-- `lem:print`, paper/paper.tex: the one uniform formula-variable program derives the actual role and original occurrence, then computes the complete native role metadata from the actual walk index. -/
def atomRoleProgram : St VV MM:=.seq splitAtom roleHeaderProgram

/-- `lem:print` and `prop:time`, paper/paper.tex: every parsed valid polynomial atom is physically decoded into its ORIGINAL gate occurrence and actual affine corner fields, without increasing the original child census. -/
theorem atomRoleProgram_run (C : Ctx) (G : ℕ) (i : Fin (17*G)) (a : DS VV MM)
    (hi : a.env atomValue=i.val) (hG : a.env occurrenceCount=G)
    (hpos : 0<G) (hGfit : 2*G≤2^C.Wd)
    (hr : 0<a.env WalkDigits.radix) (hrfit : 2*a.env WalkDigits.radix≤2^C.Wd)
    (hsmall : 17<2^C.Wd) :
    Hs C atomRoleProgram a 4502 (fun b=>
      RoleData (a.env WalkDigits.number) (a.env WalkDigits.radix)
        (finProdFinEquiv.symm i).1 b ∧
      b.env originalIndex=(finProdFinEquiv.symm i).2.val ∧
      b.sh=a.sh ∧ Fr a b (originalIndex::roleIndex::dispatchScratch)) := by
  unfold atomRoleProgram
  refine Hs.seq (t2:=4500) (splitAtom_run C G i a hi hG hpos hGfit) ?_
  rintro b ⟨brole,bgate,bsh,bfr⟩
  have brad : b.env WalkDigits.radix=a.env WalkDigits.radix:=bfr _ (by decide)
  have bnum : b.env WalkDigits.number=a.env WalkDigits.number:=bfr _ (by decide)
  have eb:=roleHeaderProgram_run C (finProdFinEquiv.symm i).1 b brole
    (by rw [brad];exact hr) (by rw [brad];exact hrfit) hsmall
  refine eb.mono le_rfl ?_
  rintro out ⟨od,osh,ofr⟩
  refine ⟨?_,(ofr originalIndex (by decide)).trans bgate,osh.trans bsh,?_⟩
  · simpa only [bnum,brad] using od
  · exact (bfr.weaken (by intro x hx;simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢;tauto)).trans
      (ofr.weaken (by intro x hx;exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr hx)))))

end NearQuarticWires.StagePrint.Header
