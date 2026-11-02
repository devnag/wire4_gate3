import Proof.Quartic.StageCarrierEnvelope.Width
import Proof.Quartic.StagePrintContext.Acquire

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StagePrint StagePrint.Header StageMain.Compact

/-- `lem:print`, paper/paper.tex: only the
literal finite preparation and the next binary count are parsed by
the metadata pass; every compiled entry remains an unread suffix. -/
def metadataAcquire : St VV MM := .seq initP Carrier.readContext

/-- `prop:time`, paper/paper.tex: every actual
input-length read, compact decoder and binary count instruction is paid. -/
noncomputable def metadataReadSteps {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  6+Carrier.contextCost (HeaderCall.of_print r) (r.child.cellCall.seed.N^8)
    (StageLift.preparedWordOf r).length

/-- `lem:print` and `prop:time`, paper/paper.tex: the cold actual carrier alone establishes the
original source needed by the checked affine-header computation. -/
theorem metadataAcquire_run {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (hin : C.inp=TermsCarrier.word r)
    (hW : 100*((StageLift.preparedWordOf r).length+1)≤C.Wd) :
    Hs C metadataAcquire (a0 : DS VV MM) (metadataReadSteps r) (fun b=>
      HeaderSourceData (HeaderCall.of_print r) b ∧ b.out=[] ∧ Cst b ∧ Valid C b) := by
  let P:=(StageLift.preparedWordOf r).length
  have hsource : compactInput r.child.call r.child.selected.1
      (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness)=StageLift.preparedWordOf r := rfl
  have hdecoder:=compact_decoder_bounds r.child.call r.child.selected.1
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness) C.Wd
    (by rw [hsource];omega)
  have hcount:=walk_count_bits r
  have hn:=original_arity_le r
  have hPbits:=NearCubicGates.Close.Dispatch.natBitLength_le_succ P
  have hrun : Hs C metadataAcquire (a0 : DS VV MM) (metadataReadSteps r) (fun b=>
      HeaderSourceData (HeaderCall.of_print r) b ∧ b.out=[] ∧ Cst b) := by
    unfold metadataAcquire
    refine (Hs.seq (t2:=Carrier.contextCost (HeaderCall.of_print r) (r.child.cellCall.seed.N^8) P)
      (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl
        (by have hh:=Nat.lt_two_pow_self (n:=C.Wd);omega)) ?_).mono
      (by unfold metadataReadSteps;dsimp only [P];omega) (fun _ h=>h)
    rintro a ⟨hc,hram,hrc,hip,hout,_hkin,_hkout,_hkc,_hfr⟩
    have hinput : C.inp.drop a.ip=Carrier.sourcePrefix (HeaderCall.of_print r)
        (r.child.cellCall.seed.N^8)++(List.ofFn (TermsCarrier.entryWord r)).flatten := by
      rw [hip,hin]
      simp only [a0,List.drop_zero,Carrier.sourcePrefix,Carrier.preparedWord,HeaderCall.of_print]
      rfl
    have er:=Carrier.readContext_run C (HeaderCall.of_print r) (r.child.cellCall.seed.N^8) P
      (List.ofFn (TermsCarrier.entryWord r)).flatten a hc hinput
      (by change natBitLength P+2≤C.Wd;dsimp only [P] at hPbits ⊢;omega)
      (by omega) hdecoder.1 hdecoder.2.1
      hdecoder.2.2.1 (by dsimp only [P];omega)
      hdecoder.2.2.2
      (by intro store _hstore;rw [hram,hrc];exact ⟨rfl,rfl⟩)
    refine er.mono le_rfl ?_
    rintro b ⟨_bip,_bn,_bl,_bram,_brc,hd,hrest,hbc⟩
    exact ⟨hd,(congrArg Prod.fst hrest).trans hout,hbc⟩
  refine (StagePrint.source_addValid (by omega) (a0_valid C) hrun).mono le_rfl ?_
  rintro b ⟨⟨hd,ho,hc⟩,hv⟩
  exact ⟨hd,ho,hc,hv⟩

end NearQuarticWires.StageCarrierEnvelope
