import Proof.Quartic.StagePrint.GreedyEntryDock

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: one compiled
walk consists of its original ordinal, degree, modulus and literal
framed Terms bytes, including every zero coefficient. -/
structure Entry where
  index : ℕ
  degree : ℕ
  modulus : ℕ
  payload : List Bool

def Entry.header (r : Entry) : List ℕ := [r.index,r.degree,r.modulus]
def Entry.word (r : Entry) : List Bool := r.header.flatMap natWord++frame r.payload

/-- `lem:print`, paper/paper.tex: the finite
entry description is determined by the actual compiled source. -/
noncomputable def actualEntry {B1 B2 : ℕ} (r : StagePrint.GreedyEntry.Request B1 B2) : Entry :=
  ⟨r.index.val,r.degree,r.modulus,termsWord r.terms⟩

theorem actualEntry_word {B1 B2 : ℕ} (r : StagePrint.GreedyEntry.Request B1 B2) :
    (actualEntry r).word=StagePrint.TermsCarrier.entryWord r.source r.index := by
  simp only [actualEntry,Entry.word,Entry.header,StagePrint.TermsCarrier.entryWord,
    StagePrint.GreedyEntry.Request.degree,StagePrint.GreedyEntry.Request.modulus,
    StagePrint.GreedyEntry.Request.terms,StageLift.sourceWalkPacket,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

/-- `lem:print`, paper/paper.tex: each entry
begins with the natural-code marker, independently of its ordinal. -/
theorem Entry.word_cons (r : Entry) : ∃ tail,r.word=true::tail := by
  have hpos : 1≤natBitLength r.index := by unfold natBitLength;omega
  have hn : ∃ tail,natWord r.index=true::tail := by
    rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_eq]
    generalize natBitLength r.index=bits at *
    cases bits with
    | zero=>omega
    | succ bits=>exact ⟨_,rfl⟩
  obtain ⟨tail,ht⟩:=hn
  simp only [Entry.word,Entry.header,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    ht,List.cons_append]
  exact ⟨_,rfl⟩

end NearQuarticWires.StageGreedyCollector
