import Proof.Quartic.StageCertificateFinal.NativeTables
import Proof.Quartic.StageCertificateControl.CertificateBatch

/-!
# The literal complete list of generated certificate tests

Paper: `lem:print`, paper/paper.tex,
and Step 2 of `sec:algorithm`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms.SInt (encS)
open StageCertificateControl

/-- `sec:params` and `sec:algorithm`, paper/paper.tex: every actually visited test has the same
uniquely prepared parameter data as its original selected call. -/
theorem family_parameters_eq (B1 B2 : ℕ) (c : Call) (w : List Bool)
    (j : Fin (certificatePoolFamily B1 B2 (c,w)).count) (p : Program.Selected c) :
    ((certificatePoolFamily B1 B2 (c,w)).request j).prepared.selected.1=p.1 := by
  let r := (certificatePoolFamily B1 B2 (c,w)).request j
  have hc := (certificatePoolFamily_request B1 B2 (c,w) j).1
  change r.prepared.call=c at hc
  have hp := congrArg (fun c => Cells.prepare (Builder.callInput c)) hc
  exact Option.some.inj (r.prepared.selected.2.symm.trans (hp.trans p.2))

/-- `sec:algorithm`, paper/paper.tex: the native
certificate consumer receives every complete generated test in the
exact physically enumerated whole-test order, including empty default. -/
noncomputable def tests {B1 B2 : ℕ} (tables : NativeTables B1 B2) (c : Call) (w : List Bool) :
    List NativeTest :=
  List.ofFn (fun j : Fin (certificatePoolFamily B1 B2 (c,w)).count =>
    let r := (certificatePoolFamily B1 B2 (c,w)).request j
    tableTest r.metadata.threshold (tables.table r))

/-- `sec:algorithm`, paper/paper.tex: the actual
native test list has exactly the physically computed whole-test count. -/
theorem tests_count {B1 B2 : ℕ} (tables : NativeTables B1 B2) (c : Call) (w : List Bool) :
    (tests tables c w).length=countHeaderValue B1 B2 c := by
  rw [tests,List.length_ofFn,certificatePoolFamily_count]

/-- `lem:print`, paper/paper.tex: every entry
of every generated signed native test fits its emitted width on all
witnesses, before any certificate filtering is performed. -/
theorem tests_values_fit {B1 B2 : ℕ} (tables : NativeTables B1 B2) (c : Call) (w : List Bool) :
    ∀test∈tests tables c w,∀z∈test.values,encS z<2^test.width := by
  intro test ht
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
  exact tableTest_values_fit _ _

/-- `lem:print` and `sec:algorithm`, paper/paper.tex: every complete generated test retains the
full original call's padded native census, with no intermediate crop. -/
theorem tests_lengths {B1 B2 : ℕ} (tables : NativeTables B1 B2) (c : Call) (w : List Bool)
    (p : Program.Selected c) :
    ∀test∈tests tables c w,test.values.length=paddedCount c.n p.1.k := by
  intro test ht
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
  let r := (certificatePoolFamily B1 B2 (c,w)).request j
  have hc := (certificatePoolFamily_request B1 B2 (c,w) j).1
  have hp := family_parameters_eq B1 B2 c w j p
  change r.prepared.call=c at hc
  change r.prepared.selected.1=p.1 at hp
  change (tableTest r.metadata.threshold (tables.table r)).values.length=_
  rw [tableTest_count,tables.count,hp,hc]

/-- `prop:time`, paper/paper.tex: the
original-arity native width bound applies to every actually generated
test and to the same original call in the cold bitmap allocator. -/
theorem tests_widths {B1 B2 : ℕ} (tables : NativeTables B1 B2) (c : Call) (w : List Bool) :
    ∀test∈tests tables c w,test.width≤tables.coefficient*(c.n+1)^tables.degree := by
  intro test ht
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
  let r := (certificatePoolFamily B1 B2 (c,w)).request j
  have hc := (certificatePoolFamily_request B1 B2 (c,w) j).1
  change r.prepared.call=c at hc
  change (tables.table r).q+1≤_
  simpa only [hc] using tables.width r

end NearQuarticWires.StageCertificateFinal
