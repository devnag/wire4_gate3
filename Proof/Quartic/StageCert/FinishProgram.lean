import Proof.Quartic.StageCert.ColumnStream

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTablesProg (cstInit)

/-- `sec:algorithm`, paper/paper.tex: the dispatch flag controls
whether the certified-column frame is appended to the preserved payload. -/
def appendFlag : Fin VV := ⟨49, by decide⟩

/-- `sec:algorithm`, paper/paper.tex: close the certificate frame
inside the outer stage frame. -/
def closeCertificate : St VV MM :=
  .seq (.op (.emit true)) (.seq (.op (.emit false)) (.op (.emit false)))

/-- `sec:algorithm`, paper/paper.tex: append the complete
certified-column frame to a prepared outer frame. -/
def appendColumns : St VV MM :=
  .seq (readInto columnCount) (.seq (.op (.zero columnIndex))
    (.seq columnStream closeCertificate))

/-- `sec:algorithm`, paper/paper.tex: the physical global
certificate finisher parses the table stream, preserves the preparation word,
reduces each column and writes the framed next-stage word. -/
def finishProgram : St VV MM :=
  .seq cstInit (.seq rdNatI (.seq (readInto payloadLength)
    (.seq (.op (.zero payloadIndex)) (.seq copyPayload (.seq (readInto appendFlag)
      (.ite (.eq appendFlag vZ) (.op (.emit false))
        appendColumns))))))

/-- `sec:algorithm`, paper/paper.tex: the delimiter routine adds
exactly the two nested frame terminators. -/
theorem closeCertificate_run (C : Ctx) (a : DS VV MM) :
    Hs C closeCertificate a 5 (fun b => b.out = a.out ++ [true,false,false]) := by
  unfold closeCertificate
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_emit C true a) (fun b hb => ?_)
  subst b
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_emit C false _) (fun c hc => ?_)
  subst c
  refine (hs_emit C false _).mono le_rfl ?_
  intro d hd
  subst d
  simp [List.append_assoc]

end NearQuarticWires.StageCert
