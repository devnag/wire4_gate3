import Proof.Quartic.StageCertificateControl.IndexedNative
import Proof.Quartic.StageCertificateControl.CountMachine
import Proof.Quartic.StagePrint.PoolFamily

/-!
# The actual all-calls family of complete certificate tests

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
the default in `sec:params`, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageCertTests

/-- `sec:algorithm` and the default in `sec:params`,
paper/paper.tex: successful dispatch enumerates
every actual whole-test metadata index on the same original source;
default dispatch has an empty physical test family. -/
noncomputable def certificatePoolFamily (B1 B2 : ℕ) (r : Call×List Bool) :
    StagePrint.PoolFamily (IndexedRequest B1 B2) IndexedRequest.word :=
  match hd : Program.dispatch B1 B2 r.1 with
  | none =>
    { count := 0
      source := Program.prepWord B1 B2 r.1 r.2
      request := fun j => Fin.elim0 j
      indexed := fun j => Fin.elim0 j }
  | some p =>
    { count := (certificateMetadata p.1 r.1.kind).length
      source := Program.prepWord B1 B2 r.1 r.2
      request := fun j => ⟨⟨r.1,r.2,p,hd⟩,j⟩
      indexed := fun _ => rfl }

/-- `sec:algorithm`, paper/paper.tex: every indexed
whole-test input uses the original retained preparation word. -/
theorem certificatePoolFamily_source (B1 B2 : ℕ) (r : Call×List Bool) :
    (certificatePoolFamily B1 B2 r).source=countWord B1 B2 r := by
  unfold certificatePoolFamily
  split <;> rfl

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the family count agrees exactly with the
actual cold count machine, including zero on default dispatch. -/
theorem certificatePoolFamily_count (B1 B2 : ℕ) (r : Call×List Bool) :
    (certificatePoolFamily B1 B2 r).count=countHeaderValue B1 B2 r.1 := by
  unfold certificatePoolFamily countHeaderValue
  split <;> rename_i hd <;> simp [hd]

/-- `sec:algorithm`, paper/paper.tex: every actually
visited test retains the same original call and entire original witness
parameter; no conditional source or child call replaces it. -/
theorem certificatePoolFamily_request (B1 B2 : ℕ) (r : Call×List Bool)
    (j : Fin (certificatePoolFamily B1 B2 r).count) :
    ((certificatePoolFamily B1 B2 r).request j).prepared.call=r.1 ∧
      ((certificatePoolFamily B1 B2 r).request j).prepared.witness=r.2 := by
  revert j
  unfold certificatePoolFamily
  split
  · intro j;exact Fin.elim0 j
  · intro j;exact ⟨rfl,rfl⟩

end NearQuarticWires.StageCertificateControl
