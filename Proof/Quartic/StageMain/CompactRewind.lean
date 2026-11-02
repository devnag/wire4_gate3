import Proof.Quartic.StageMain.CompactPrepare

/-!
# Returning across the finite preparation prefix

Step 4 of `sec:algorithm`, paper/paper.tex,
can decode its retained finite source without traversing the certificate
bitmap. The return distance is the actual length already computed by
the source scanner, and every backward input move is charged.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Compact

open NearCubicGates.Close.Cells

def rewindCompact : St VV MM :=
  .seq (.op (.copy StageRecovery.tokenLengthVar compactLength)) StageRecovery.inputReturnProgram

theorem rewindCompact_run (C : Ctx) (base L : ℕ) (a : DS VV MM) (hc : Cst a)
    (hip : a.ip = base + L) (hlen : a.env compactLength = L) (hfit : L < 2 ^ C.Wd) :
    Hs C rewindCompact a (5 * L + 6) (fun b =>
      b.ip = base ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [StageRecovery.tokenLengthVar, StageRecovery.inputReturnIndex]) := by
  unfold rewindCompact
  refine (Hs.seq (t1 := 1) (t2 := 5 * L + 4)
    (hs_copy C StageRecovery.tokenLengthVar compactLength a (by decide)) ?_).mono
    (by omega) (fun _ h => h)
  rintro b rfl
  let d := a.set StageRecovery.tokenLengthVar (a.env compactLength)
  have hdf : Fr a d [StageRecovery.tokenLengthVar] := Fr.set a _ (by simp)
  have hdc := Cst.of_fr hc hdf (by decide)
  refine (StageRecovery.inputReturnProgram_spec C d L base
    (by simpa [d] using hlen) hip hfit).mono le_rfl ?_
  rintro e ⟨heip, herest, hefr⟩
  exact ⟨heip, herest, Cst.of_fr hdc hefr (by decide),
    (hdf.weaken (by simp)).trans (hefr.weaken (by simp))⟩

end NearQuarticWires.StageMain.Compact
