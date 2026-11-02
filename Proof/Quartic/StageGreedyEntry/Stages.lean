import Proof.Quartic.StageGreedyEntry.Rows
import Proof.Quartic.StageGreedyEntry.Budget
import Proof.Quartic.StageGreedyCollector.Requests
import Proof.Quartic.StageEqualityRows.Final
import Proof.Quartic.StageCertificateControl.NativePrefixMachine

/-!
# The ordinary stages of one actual entry

Paper: `lem:print` and `lem:residue`, paper/paper.tex.

Each stage is an ordinary word function on the actual entry request. Write `w = (n+1)/2` (the dense
width, `width_eq`), `q` for the modulus, `W` for the stack width, `TW` for the tuple request word and
`x` for the tuple records. The stages are:
`prefixStage` (word ↦ `w, q, word`), `formatStage` (↦ `w, q, TW`), `stackStage` (↦ `w, q, W, TW`),
`tupleStage` (↦ `w, q, W, x`), `rowsStage` (↦ `w, q, W, equality-row input`),
`equalityStage` (↦ `w, q, W, signed weak stream`), then the modular input and the modular reducer
`modularStage`. Every retained natural is carried by the cold prefix wrapper
`StageCertificateControl.nativePrefixWordFunction`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open StagePrint StageGreedyCollector

/-- `prop:time`, paper/paper.tex: the same program under equal words and a larger clock. -/
noncomputable def recast {Request : Type} {input input' output output' : Request→List Bool}
    {budget budget' : Request→ℕ} (f : WordFunction Request input output budget)
    (hi : ∀r,input r=input' r) (ho : ∀r,output r=output' r) (hb : ∀r,budget r≤budget' r) :
    WordFunction Request input' output' budget' :=
  StageEqualityRows.enlargeBudget
    (⟨f.program,fun r=>by rw [←hi r,←ho r];exact f.realizes r⟩ : WordFunction Request input' output' budget) hb

/-- `lem:print`, paper/paper.tex: an ordinary word function read on derived requests. -/
def comap {Request Request' : Type} {input output : Request→List Bool} {budget : Request→ℕ}
    (f : WordFunction Request input output budget) (g : Request'→Request) :
    WordFunction Request' (fun r=>input (g r)) (fun r=>output (g r)) (fun r=>budget (g r)) :=
  ⟨f.program,fun r=>f.realizes (g r)⟩

variable (B1 B2 : ℕ)

/-- The dense width of the original star, `⌈n/2⌉`. -/
def wd {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) : ℕ := (r.source.child.call.n+1)/2

theorem wd_eq {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    PrimT.C4Geo.width r.rowContext.header.prepared.starParams=wd r :=
  width_eq _

/-- `lem:print`, paper/paper.tex: retained dense width and modulus. -/
noncomputable def prefixStage :
    WordFunction (GreedyEntry.Request B1 B2) (fun r=>(EntryFormat.ofGreedy r).word)
      (fun r=>frame (natWord (wd r)++(natWord r.modulus++(EntryFormat.ofGreedy r).word)))
      (fun r=>2*prefixCost (EntryFormat.ofGreedy r).word.length r.source.child.call.n+2) :=
  recast (prefixWordFunction B1 B2) (fun _=>rfl) (fun _=>by simp [wd,List.append_assoc]) (fun _=>le_rfl)

/-- `lem:print`, paper/paper.tex: the closed formatter under the two retained naturals. -/
noncomputable def formatStage :=
  StageCertificateControl.nativePrefixWordFunction
    (StageCertificateControl.nativePrefixWordFunction (formatter B1 B2) (fun r=>r.modulus)) wd

/-- `lem:print`, paper/paper.tex: the stack width is retained from the formatted request. -/
noncomputable def stackStage :
    WordFunction (GreedyEntry.Request B1 B2) (fun r=>natWord (wd r)++(natWord r.modulus++r.termRequest.word))
      (fun r=>frame (natWord (wd r)++(natWord r.modulus++(natWord r.termRequest.stackWidth++r.termRequest.word))))
      (fun r=>2*stackCost (natWord (wd r)++(natWord r.modulus++r.termRequest.word)).length+2) :=
  wordFunction_of_ideal (.wm stackP) 1 (by decide)
    (fun r=>10*((natWord (wd r)++(natWord r.modulus++r.termRequest.word)).length+1)) (fun _ _=>0)
    (fun r=>stackCost (natWord (wd r)++(natWord r.modulus++r.termRequest.word)).length) (fun _=>le_rfl)
    (fun r=>⟨rfl,by
      obtain ⟨τ,he,ho⟩:=stackP_run (wd r) r.modulus r.termRequest
      exact ⟨τ,WXExec.wm he,ho⟩⟩)

/-- `lem:print`, paper/paper.tex: the tuple call under the three retained naturals. -/
noncomputable def tupleStage {tb : StageTuple.TermCutRequest→ℕ}
    (tuple : WordFunction StageTuple.TermCutRequest StageTuple.TermCutRequest.word (fun t=>frame t.output) tb) :=
  StageCertificateControl.nativePrefixWordFunction
    (StageCertificateControl.nativePrefixWordFunction
      (StageCertificateControl.nativePrefixWordFunction
        (comap tuple (fun r : GreedyEntry.Request B1 B2=>r.termRequest)) (fun r=>r.termRequest.stackWidth))
      (fun r=>r.modulus)) wd

/-- `lem:print`, paper/paper.tex: the literal equality-row input. -/
theorem rows_input {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    Top.loadRec r.termRequest.output (List.replicate (wd r) true) (List.replicate r.termRequest.stackWidth true)
      [] [] [] [] [] [] [] []=Downstream.equalityRowsInput (equalityRequest r) := by
  rw [equalityRequest_input,wd_eq]

/-- `lem:print`, paper/paper.tex: the equality-row input built in place. -/
noncomputable def rowsStage :
    WordFunction (GreedyEntry.Request B1 B2)
      (fun r=>natWord (wd r)++(natWord r.modulus++(natWord r.termRequest.stackWidth++r.termRequest.output)))
      (fun r=>frame (natWord (wd r)++(natWord r.modulus++(natWord r.termRequest.stackWidth++
        Downstream.equalityRowsInput (equalityRequest r)))))
      (fun r=>2*rowsCost (natWord (wd r)++(natWord r.modulus++(natWord r.termRequest.stackWidth++
        r.termRequest.output))).length (wd r) r.termRequest.stackWidth+2) :=
  wordFunction_of_ideal (.wm rowsP) 1 (by decide)
    (fun r=>10*((natWord (wd r)++(natWord r.modulus++(natWord r.termRequest.stackWidth++
      r.termRequest.output))).length+1)+8*(wd r+r.termRequest.stackWidth+2)) (fun _ _=>0)
    (fun r=>rowsCost (natWord (wd r)++(natWord r.modulus++(natWord r.termRequest.stackWidth++
      r.termRequest.output))).length (wd r) r.termRequest.stackWidth) (fun _=>le_rfl)
    (fun r=>⟨rfl,by
      obtain ⟨τ,he,ho⟩:=rowsP_run (wd r) r.modulus r.termRequest.stackWidth r.termRequest.output
      rw [rows_input] at ho
      exact ⟨τ,WXExec.wm he,ho⟩⟩)

/-- `lem:print`, paper/paper.tex: the sealed equality-row constructor under the
three retained naturals; its reply is the signed weak stream of the modular request. -/
noncomputable def equalityStage :=
  StageCertificateControl.nativePrefixWordFunction
    (StageCertificateControl.nativePrefixWordFunction
      (StageCertificateControl.nativePrefixWordFunction
        (comap StageEqualityRows.equalityRowsPrinter (fun r : GreedyEntry.Request B1 B2=>equalityRequest r) :
          WordFunction (GreedyEntry.Request B1 B2) (fun r=>Downstream.equalityRowsInput (equalityRequest r))
            (fun r=>frame (modularRequest r).stream) _)
        (fun r=>r.termRequest.stackWidth))
      (fun r=>r.modulus)) wd

/-- `lem:residue` and `lem:print`, paper/paper.tex: the sealed modular
reducer writes exactly the final per-entry body. -/
noncomputable def modularStage :
    WordFunction (GreedyEntry.Request B1 B2) (fun r=>(modularRequest r).word) entryOutput
      (fun r=>10^30*((modularRequest r).width+(modularRequest r).fieldWidth+natBitLength (modularRequest r).modulus+2)^20*
        ((modularRequest r).stream.length+1)) :=
  recast (comap StageModularSetup.modularCutsPrinter (fun r : GreedyEntry.Request B1 B2=>modularRequest r))
    (fun _=>rfl) (fun r=>modularRequest_output r) (fun _=>le_rfl)

end NearQuarticWires.StageGreedyEntry
