import Proof.Quartic.StagePrint.RoleProgram

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Header
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the actual polynomial-variable quotient determines one of the seventeen offset roles. -/
def roleIndex : Fin VV:=97
def roleSelector : Fin VV:=114

/-- `lem:print`, paper/paper.tex: a fixed finite conditional program selects the actual offset branch; no decoded geometric provider is used. -/
def roleDispatch : List (Fin 17)→St VV MM
  | []=>skipS
  | role::roles=>.seq (smallLiteral roleSelector role.val)
      (.ite (.eq roleIndex roleSelector) (literalRoleProgram role) (roleDispatch roles))

/-- `lem:print`, paper/paper.tex: all seventeen literal edge, vertex and center branches belong to the one uniform physical program. -/
def roleHeaderProgram : St VV MM:=roleDispatch (List.finRange 17)

/-- `lem:print`, paper/paper.tex: only the finite selector and actual role-output/division fields may change during dispatch. -/
def dispatchScratch : List (Fin VV):=roleSelector::roleScratch

/-- `lem:print` and `prop:time`, paper/paper.tex: every selector assignment and failed branch is charged, and the matching branch computes the actual walk patterns. -/
theorem roleDispatch_run (C : Ctx) :
    ∀ (roles : List (Fin 17)) (role : Fin 17) (a : DS VV MM), role∈roles→
      a.env roleIndex=role.val→0<a.env WalkDigits.radix→
      2*a.env WalkDigits.radix≤2^C.Wd→17<2^C.Wd→
      Hs C (roleDispatch roles) a ((roles.length+1)*250) (fun b=>
        RoleData (a.env WalkDigits.number) (a.env WalkDigits.radix) role b ∧
        b.sh=a.sh ∧ Fr a b dispatchScratch)
  | [],role,a,hm,_hi,_hr,_hfit,_hs=>by simp at hm
  | head::tail,role,a,hm,hi,hr,hfit,hs=>by
    unfold roleDispatch
    refine (Hs.seq (t2:=(tail.length+1)*250+2)
      (smallLiteral_run C roleSelector head.val a (by have:=head.isLt;omega)) ?_).mono
      (by simp only [List.length_cons];have:=head.isLt;omega) (fun _ h=>h)
    rintro b rfl
    let b:=a.set roleSelector head.val
    have bsel : b.env roleSelector=head.val:=by simp [b]
    have bidx : b.env roleIndex=role.val:=by simpa [b,roleIndex,roleSelector] using hi
    have brad : b.env WalkDigits.radix=a.env WalkDigits.radix:=by rfl
    have bnum : b.env WalkDigits.number=a.env WalkDigits.number:=by rfl
    have bf : Fr a b dispatchScratch:=Fr.set a _ (by simp [dispatchScratch])
    refine Hs.ite (by decide : roleIndex≠roleSelector) (fun heq=>?_) (fun hne=>?_)
    · have he : role=head:=Fin.ext (by
        change decide (b.env roleIndex=b.env roleSelector)=true at heq
        rw [bidx,bsel] at heq
        exact of_decide_eq_true heq)
      subst he
      have eb:=literalRoleProgram_run C role b (by rw [brad];exact hr)
        (by rw [brad];exact hfit) hs
      refine eb.mono (by omega) ?_
      rintro out ⟨od,osh,ofr⟩
      refine ⟨?_,osh, bf.trans (ofr.weaken (by intro x hx;exact List.mem_cons.mpr (Or.inr hx)))⟩
      simpa only [bnum,brad] using od
    · have hn : role≠head:=by
        intro he
        subst he
        change decide (b.env roleIndex=b.env roleSelector)=false at hne
        rw [bidx,bsel] at hne
        simp at hne
      have htail : role∈tail:=by simpa only [List.mem_cons,hn,false_or] using hm
      have eb:=roleDispatch_run C tail role b htail bidx (by rw [brad];exact hr)
        (by rw [brad];exact hfit) hs
      refine eb.mono (by omega) ?_
      rintro out ⟨od,osh,ofr⟩
      refine ⟨?_,osh,bf.trans ofr⟩
      simpa only [bnum,brad] using od

/-- `lem:print` and `prop:time`, paper/paper.tex: one fixed cold-compatible branch tree handles every valid polynomial atom role at a uniform constant source clock. -/
theorem roleHeaderProgram_run (C : Ctx) (role : Fin 17) (a : DS VV MM)
    (hi : a.env roleIndex=role.val) (hr : 0<a.env WalkDigits.radix)
    (hfit : 2*a.env WalkDigits.radix≤2^C.Wd) (hs : 17<2^C.Wd) :
    Hs C roleHeaderProgram a 4500 (fun b=>
      RoleData (a.env WalkDigits.number) (a.env WalkDigits.radix) role b ∧
      b.sh=a.sh ∧ Fr a b dispatchScratch) := by
  simpa only [roleHeaderProgram,List.length_finRange] using
    roleDispatch_run C (List.finRange 17) role a (List.mem_finRange role) hi hr hfit hs

end NearQuarticWires.StagePrint.Header
