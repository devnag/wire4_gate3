import Proof.Quartic.StageCertNative.PrefixMachine
import Proof.Quartic.StageCertNative.EntryRequest

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces.Formats

noncomputable def entrySourcePairBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  2*StageRecovery.FramedPair.cost (input:=nFirstWord)
    (left:=exactPrefixWord)
    (right:=fun r : TermJob B1 B2=>frame (termsWord (exactTerms r.moment)))
    (lb:=prefixBudget) (rb:=nFirstNestedTermsBudget) r+2

/-- `lem:print`, paper/paper.tex: physical
prefix construction and exact signed Terms expansion assemble the
unchanged original native formatter input, including its counted frame. -/
noncomputable def entrySourcePairWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) nFirstWord
      (fun r=>frame (exactEntry r.moment).word) entrySourcePairBudget := by
  let f:=StageRecovery.FramedPair.wordFunction (prefixWordFunction B1 B2)
    (nFirstNestedTermsWordFunction B1 B2)
  refine ⟨f.program,?_⟩
  intro r
  have hout : exactPrefixWord r++frame (termsWord (exactTerms r.moment))=
      (exactEntry r.moment).word := by
    have hh:=actualEntry_word r.base r.index
    change (exactEntry r.moment).word=_ at hh
    rw [hh]
    simp only [exactPrefixWord,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.append_assoc]
    rfl
  simpa only [entrySourcePairBudget,hout] using f.realizes r

noncomputable def entrySourceBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  4*nFirstSourceBudget r+4*entrySourcePairBudget r+12

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual counted original source alone determines
the complete exact native formatter word, with every preprocessing,
expansion, binary-field read and frame operation physically charged. -/
noncomputable def entrySourceWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word
      (fun r=>frame (exactEntry r.moment).word) entrySourceBudget :=
  Program.WordFunction.pipe (nFirstSourceWordFunction B1 B2) (entrySourcePairWordFunction B1 B2)

end NearQuarticWires.StageCertNative
