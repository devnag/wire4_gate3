import Proof.Quartic.StageCert.Records

set_option autoImplicit false

namespace NearQuarticWires.StageCert
attribute [local instance] Classical.propDecidable
open NearQuarticWires
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex: a literal
signed strict test is represented by one Boolean. -/
noncomputable def recordPass (r : MomentRecord) : Bool := decide (r.1 < (r.2 : ℤ))

/-- `sec:algorithm`, paper/paper.tex: a column is retained exactly
when every test record passes. -/
noncomputable def columnPass (rs : List MomentRecord) : Bool := rs.all recordPass

/-- `lem:certify`, paper/paper.tex: the record reducer agrees
with the complete certificate, including every active sign pattern. -/
theorem columnPass_eq_certificate {N J : ℕ} (k : ℕ) (D : Walks.WalkData N 4 J) :
    columnPass (columnRecords k D) = decide (Walks.ColumnCertificate (by norm_num) k D) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [columnPass, List.all_eq_true, recordPass, decide_eq_true_eq]
  exact columnRecords_pass_iff k D

/-- `sec:algorithm`, paper/paper.tex: the exact table stream
contains the preserved preparation word and column-major signed moments. -/
structure CertTableRequest where
  payload : List Bool
  doAppend : Bool
  columns : List (List MomentRecord)

/-- `prop:time`, paper/paper.tex: scalar fields whose binary
heights determine the certificate stream's arithmetic width. -/
def scalarFields (r : CertTableRequest) : List ℕ :=
  r.payload.length :: r.columns.length :: (if r.doAppend then 1 else 0) ::
    r.columns.flatMap (fun rs => rs.length :: rs.flatMap
      (fun t => [if t.1 < 0 then 1 else 0, t.1.natAbs, t.2]))

/-- `prop:time`, paper/paper.tex: arithmetic width depends
on field heights rather than the number of columns. -/
def tableWidth (r : CertTableRequest) : ℕ :=
  4 + ((scalarFields r).map natBitLength).foldl max 0

/-- `sec:algorithm`, paper/paper.tex: the physical table
format uses self-delimiting integers and explicit column/test counts. -/
def certTableWord (r : CertTableRequest) : List Bool :=
  natWord (tableWidth r) ++ natWord r.payload.length ++ r.payload ++
    natWord (if r.doAppend then 1 else 0) ++ listWord (listWord momentRecordWord) r.columns

/-- `sec:algorithm`, paper/paper.tex: the exact certificate output,
with every nondispatched preparation word passed through unchanged. -/
noncomputable def certTableOutput (r : CertTableRequest) : List Bool :=
  frame (r.payload ++ if r.doAppend then frame (r.columns.map columnPass) else [])

/-- `sec:algorithm`, paper/paper.tex: the concrete table
request for a call and its retained witness prefix. -/
noncomputable def callTableRequest (B1 B2 : ℕ) (c : Call) (w : List Bool) : CertTableRequest where
  payload := Program.prepWord B1 B2 c w
  doAppend := (Program.dispatch B1 B2 c).isSome
  columns := match Program.dispatch B1 B2 c with
    | none => []
    | some p => List.ofFn (fun z => columnRecords (Program.runCall c p w).k
        ((Program.runCall c p w).column z))

/-- `sec:algorithm`, paper/paper.tex: specializing the physical
record reducer gives exactly the top-level certificate stage word. -/
theorem certTableOutput_call (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    certTableOutput (callTableRequest B1 B2 c w) = frame (Program.certWord B1 B2 c w) := by
  classical
  unfold certTableOutput callTableRequest Program.prepWord Program.certWord Program.stageWord
  cases hd : Program.dispatch B1 B2 c with
  | none => simp
  | some p =>
    simp [List.map_ofFn, Function.comp_def, columnPass_eq_certificate,
      Program.certifiedBits, Algorithm.CellCall.certifiedColumns,
      Algorithm.CellCall.Certified, List.append_assoc]

end NearQuarticWires.StageCert
