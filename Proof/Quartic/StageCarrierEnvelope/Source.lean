import Proof.Quartic.StageCarrierEnvelope.Data
import Proof.Quartic.StageCarrierEnvelope.Width
import Proof.Wire_3_5.PrimAsmParseNat

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open StagePrint

/-- `lem:print`, paper/paper.tex: three
actual first-entry metadata codecs precede the modulus codec. -/
noncomputable def firstFields {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List ℕ :=
  [r.child.cellCall.seed.N^8,0,StageLift.residueDegreeBound r.child.selected.1 r.prime]

noncomputable def firstPrefix {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  natWord (StageLift.preparedWordOf r).length++StageLift.preparedWordOf r++(firstFields r).flatMap natWord

noncomputable def firstRest {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  frame (NearCubicGates.Close.Interfaces.Formats.termsWord (TermsCarrier.actualTerms r (firstIndex r)))++(entries r).tail.flatten

/-- `lem:print`, paper/paper.tex: a real
positive original walk count exposes the exact first modulus with
an unchanged arbitrary compiled-entry suffix. -/
theorem carrier_first_modulus {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    TermsCarrier.word r=firstPrefix r++natWord (r.prime^r.child.selected.1.e)++firstRest r := by
  rw [carrier_prefix]
  simp only [firstPrefix,firstFields,firstRest,TermsCarrier.entryWord,firstIndex,
    StageLift.sourceWalkPacket,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

/-- `prop:time`, paper/paper.tex: the
first physical modulus codec is already a substring of the sole
actual carrier, independently of its numerical value. -/
theorem modulus_length_le_carrier {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (natWord (r.prime^r.child.selected.1.e)).length≤(TermsCarrier.word r).length := by
  rw [carrier_first_modulus,List.length_append,List.length_append]
  omega

/-- `prop:time`, paper/paper.tex: the small
preparation and skipped first-entry codecs are part of the real input. -/
theorem prefix_length_le_carrier {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (firstPrefix r).length≤(TermsCarrier.word r).length := by
  rw [carrier_first_modulus,List.length_append,List.length_append]
  omega

/-- `imp:partition` and `prop:time`, paper/paper.tex: the physically emitted count has only
linear binary width in the original free-center dimension. -/
theorem column_codec_length {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (natWord r.child.cellCall.ncol).length≤4*r.child.call.n+3 := by
  rw [ncol_eq]
  have hb:=StageCertTests.power_bitLength_le 2 (r.child.call.n-r.child.selected.1.k)
  rw [show natBitLength 2=2 from by decide] at hb
  rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]
  omega

end NearQuarticWires.StageCarrierEnvelope
