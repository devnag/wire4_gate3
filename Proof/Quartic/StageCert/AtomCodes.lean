import Proof.Quartic.StageCert.EdgeTokens
import Proof.Quartic.Cells.Atoms

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: exact dense offset
codes for the original eight-edge, eight-vertex and center pool. -/
def cornerRoleCode (edge : Fin 8) (corner : Fin 4) : ℕ :=
  if corner.val=0 then edge.val
  else if corner.val=1 then 8+(if edge.val%2=0 then edge.val else (edge.val+1)%8)
  else if corner.val=2 then 8+(if edge.val%2=0 then (edge.val+1)%8 else edge.val)
  else 16

/-- `lem:print`, paper/paper.tex: all finite role
codes agree literally with the original `Cells.cornerRole` indexing. -/
theorem cornerRoleCode_eq (edge : Fin 8) (corner : Fin 4) :
    (Cells.offsetIndex 4 (Cells.cornerRole (by decide : 0<4) edge corner)).val=
      cornerRoleCode edge corner := by
  fin_cases edge <;> fin_cases corner <;> decide

/-- `lem:print`, paper/paper.tex: atom labels are exact
offset-major original occurrence indices, including duplicate raw gates. -/
theorem atomIndex_eq_code {G : ℕ} (edge : Fin 8) (corner : Fin 4) (g : Fin G) :
    (Cells.atomIndex (Cells.cornerRole (by decide : 0<4) edge corner) g).val=
      cornerRoleCode edge corner*G+g.val := by
  change g.val+G*(Cells.offsetIndex 4 (Cells.cornerRole (by decide : 0<4) edge corner)).val=_
  rw [cornerRoleCode_eq]
  ring

/-- `lem:print`, paper/paper.tex: the current original
offset code in the finite atom-index arithmetic. -/
def atomRole : Fin VV := ⟨95,by decide⟩
/-- `lem:print`, paper/paper.tex: all physical original
gate occurrences determine the offset-major atom stride. -/
def atomCount : Fin VV := ⟨96,by decide⟩
/-- `lem:print`, paper/paper.tex: the original occurrence
position is preserved across every role of the same walk formula. -/
def atomOccurrence : Fin VV := ⟨97,by decide⟩
/-- `lem:print`, paper/paper.tex: the exact numeric
atom index passed to the physical postfix token emitter. -/
def atomValue : Fin VV := ⟨98,by decide⟩

/-- `lem:print`, paper/paper.tex: an atom label is
computed from its actual original role, stride and occurrence position. -/
def computeAtomIndex : St VV MM :=
  .seq (.op (.mul atomRole atomCount atomValue)) (.op (.add atomValue atomOccurrence))

/-- `lem:print` and `prop:time`, paper/paper.tex: dense atom indexing is a concrete bounded binary computation. -/
theorem computeAtomIndex_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (hfit : a.env atomRole*a.env atomCount+a.env atomOccurrence<2^C.Wd) :
    Hs C computeAtomIndex a 3 (fun z=>
      z.env atomValue=a.env atomRole*a.env atomCount+a.env atomOccurrence ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc,z.out)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc,a.out) ∧
      Cst z ∧ Fr a z [atomValue]) := by
  unfold computeAtomIndex
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_mul C atomRole atomCount atomValue a (by decide) (by decide) (by decide) (by omega)) ?_
  rintro b rfl
  refine (hs_add C atomValue atomOccurrence _ (by decide)
    (by simp only [DS.set_env_self,DS.set_env_ne _ _ (by decide : atomOccurrence≠atomValue)]; exact hfit)).mono le_rfl ?_
  rintro z rfl
  refine ⟨by simp [DS.set,atomValue,atomOccurrence],rfl,?_,
    (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩
  exact ⟨by vsimp [atomValue,hc.z],by vsimp [atomValue,hc.one],by vsimp [atomValue,hc.two]⟩

end NearQuarticWires.StageCert.Tokens
