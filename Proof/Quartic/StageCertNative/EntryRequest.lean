import Proof.Quartic.StageCertNative.ExactSource
import Proof.Quartic.StageCertNative.Ordinal
import Proof.Quartic.StageCert.MomentNativeContext
import Proof.Quartic.StageCert.MomentNativeBits
import Proof.Quartic.StagePrint.EntryFormatRequest
import Proof.Quartic.StagePrint.ContextTarget

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Tabulator
open StageCert.Tokens StageCertificateControl

/-- `lem:print`, paper/paper.tex: exact native
coefficients are the actual output of the integer expansion machine;
their bit bound holds on every original proposed witness. -/
noncomputable def exactEntry {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    StagePrint.EntryFormat.Request false where
  toRowContext:=r.nativeContext
  terms:=exactTerms r
  degree:=r.packet.degree
  scale:=Cells.nativeCertificateBits B1 r.call.n
  terms_nodup:=NearCubicGates.Close.Expand.expansionMachine.ok ⟨_,r.formula⟩ |>.nodup
  terms_degree:=by
    intro S hS
    exact ((NearCubicGates.Close.Expand.expansionMachine.ok ⟨_,r.formula⟩).degree S hS).trans
      r.formula_degree
  coefficient_bits:=by
    intro t ht
    exact (r.expansion_coefficient_bits t ht).1

/-- `lem:print`, paper/paper.tex:
all terms reuse the single context computed from the original BASE
preparation; no native bank or extra geometry enters the input. -/
theorem actualEntry_context {B1 B2 : ℕ} (r : IndexedRequest B1 B2)
    (i : Fin (termCount r)) :
    (exactEntry (actualMoment r i)).contextWord=StagePrint.Context.word r.prepared := by
  unfold StagePrint.EntryFormat.Request.contextWord StagePrint.EntryFormat.Request.countsWord
    StagePrint.Context.word StagePrint.Context.countsWord
  rw [Cells.ParameterRules.seed_N]
  rfl

/-- `lem:print`, paper/paper.tex: the literal
exact-mode tuple formatter receives the actual common context, actual
low-first ordinal, selected degree and polynomial coefficient bits. -/
theorem actualEntry_word {B1 B2 : ℕ} (r : IndexedRequest B1 B2)
    (i : Fin (termCount r)) :
    (exactEntry (actualMoment r i)).word=
      natWord r.prepared.call.n++StagePrint.Context.word r.prepared++natWord i.val++
      natWord (16*r.prepared.selected.1.Xmax+8*r.prepared.selected.1.k)++
      natWord (Cells.nativeCertificateBits B1 r.prepared.call.n)++
      frame (termsWord (exactTerms (actualMoment r i))) := by
  rw [StagePrint.EntryFormat.Request.word,actualEntry_context]
  rfl

end NearQuarticWires.StageCertNative
