import Proof.Quartic.StagePrintTuple.RoleFields

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicGates.Close.Cells
open StagePrint.Header

/-- `lem:print`, paper/paper.tex:
the original occurrence count is computed from the actual two banks,
then the literal atom division and walk-role decoder are executed. -/
def computeRole : St VV MM :=
  .seq (.op (.copy occurrenceCount firstBankCount))
    (.seq (.op (.add occurrenceCount secondBankCount)) atomRoleProgram)

/-- `lem:print` and `prop:time`, paper/paper.tex: the physical role computation yields the
actual original occurrence and complete corner metadata without
changing any retained affine scalar, source tape or output. -/
theorem computeRole_spec (C : Ctx) (r : RolePacket) (a : DS VV MM)
    (hfirst : a.env firstBankCount = r.firstCount)
    (hsecond : a.env secondBankCount = r.secondCount)
    (hatom : a.env atomValue = r.atom.val)
    (hradix : a.env WalkDigits.radix = r.radix)
    (haddress : a.env WalkDigits.number = r.address)
    (hpos : 0 < r.radix)
    (hGfit : 2 * (r.firstCount + r.secondCount) ≤ 2 ^ C.Wd)
    (hrfit : 2 * r.radix ≤ 2 ^ C.Wd) (hsmall : 17 < 2 ^ C.Wd) :
    Hs C computeRole a 4506 (fun b =>
      RoleData r.address r.radix (finProdFinEquiv.symm r.atom).1 b ∧
      b.env originalIndex = (finProdFinEquiv.symm r.atom).2.val ∧
      b.sh = a.sh ∧
      Fr a b (occurrenceCount :: originalIndex :: roleIndex :: dispatchScratch)) := by
  have hG : 0 < r.firstCount + r.secondCount := by have := r.atom.isLt; omega
  unfold computeRole
  refine (Hs.seq (t2:=4504)
    (hs_copy C occurrenceCount firstBankCount a (by decide)) ?_).mono
    (by omega) (fun _ h=>h)
  rintro b rfl
  let b := a.set occurrenceCount (a.env firstBankCount)
  have eb := hs_add C occurrenceCount secondBankCount b (by decide) (by
    simp only [b,DS.set_env_self,DS.set_env_ne _ _ (by decide : secondBankCount ≠ occurrenceCount)]
    rw [hfirst,hsecond]
    omega)
  refine Hs.seq (t2:=4502) eb ?_
  rintro d rfl
  let d := b.set occurrenceCount (b.env occurrenceCount + b.env secondBankCount)
  have df : Fr a d [occurrenceCount] :=
    (Fr.set a _ (by simp)).trans (Fr.set b _ (by simp))
  have dg : d.env occurrenceCount = r.firstCount + r.secondCount := by
    simp only [d,DS.set_env_self,b,DS.set_env_self,
      DS.set_env_ne _ _ (by decide : secondBankCount ≠ occurrenceCount),hfirst,hsecond]
  have ed := atomRoleProgram_run C (r.firstCount+r.secondCount) r.atom d
    (by rw [df _ (by decide)]; exact hatom) dg hG hGfit
    (by rw [df _ (by decide),hradix];exact hpos)
    (by rw [df _ (by decide),hradix];exact hrfit) hsmall
  refine ed.mono le_rfl ?_
  rintro out ⟨od,oi,osh,ofr⟩
  refine ⟨?_,oi,osh,?_⟩
  · simpa only [df _ (by decide : WalkDigits.number ∉ [occurrenceCount]),
      df _ (by decide : WalkDigits.radix ∉ [occurrenceCount]),haddress,hradix] using od
  · exact (df.weaken (by simp)).trans
      (ofr.weaken (by intro x hx;exact List.mem_cons.mpr (Or.inr hx)))

end NearQuarticWires.StageTuple
