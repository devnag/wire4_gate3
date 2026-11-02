import Proof.Quartic.StageCertNative.JobArity
import Proof.Quartic.StageCertNative.CountedTermFrames
import Proof.Quartic.StagePacketCold.Machine

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation

/-- `lem:print`, paper/paper.tex: an internal
original-arity prefix is computed from the actual original call before
allocating the polynomial-width native-header arithmetic workspace. -/
noncomputable def nFirstWord {B1 B2 : ℕ} (r : TermJob B1 B2) : List Bool :=
  natWord r.moment.call.n++r.word

noncomputable def jobIdentityWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word (fun r=>frame r.word)
      (fun r=>10^8*(r.word.length+1)^2) :=
  StagePacketCold.stripWordFunction 0 TermJob.word (fun _=>[]) TermJob.word
    (by intro r;rfl) (fun _=>rfl)

noncomputable def nFirstSourceBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  2*StageRecovery.FramedPair.cost (input:=TermJob.word)
    (left:=fun r : TermJob B1 B2=>natWord r.moment.call.n)
    (right:=TermJob.word) (lb:=jobArityBudget) (rb:=fun r=>10^8*(r.word.length+1)^2) r+2

/-- `lem:print` and `prop:time`, paper/paper.tex: the unchanged counted source is physically retained
and its actual original arity is placed first, with both source copies,
all framing and finite shared-bank cleanup included. -/
noncomputable def nFirstSourceWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word (fun r=>frame (nFirstWord r)) nFirstSourceBudget :=
  StageRecovery.FramedPair.wordFunction (jobArityWordFunction B1 B2) (jobIdentityWordFunction B1 B2)

noncomputable def nFirstProjectionBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  10^8*((nFirstWord r).length+1)^2

noncomputable def nFirstProjectionWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) nFirstWord (fun r=>frame r.word) nFirstProjectionBudget :=
  StagePacketCold.stripWordFunction 1 nFirstWord (fun r=>[r.moment.call.n]) TermJob.word
    (by intro r;simp only [nFirstWord,List.flatMap_cons,List.flatMap_nil,List.append_nil])
    (fun _=>rfl)

noncomputable def nFirstNestedTermsBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  4*nFirstProjectionBudget r+4*jobNestedTermsBudget r+12

/-- `lem:print`, paper/paper.tex: the internal
arity prefix changes neither the original exact source nor any signed
expanded Terms; it is removed by the literal binary-field projector. -/
noncomputable def nFirstNestedTermsWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) nFirstWord
      (fun r=>frame (frame (NearCubicGates.Close.Interfaces.Formats.termsWord
        (exactTerms r.moment)))) nFirstNestedTermsBudget :=
  Program.WordFunction.pipe (nFirstProjectionWordFunction B1 B2) (jobNestedTermsWordFunction B1 B2)

end NearQuarticWires.StageCertNative
