import Proof.Quartic.StageLiftTokens.TargetBounds

/-!
# Postfix operators and the actual Fermat exponent

`lem:residue`, `imp:amp` and `lem:print`, paper/paper.tex: fixed syntax tokens and the
computed prime-minus-one exponent preserve the complete retained
source and all loop counters outside the explicit printer scratch.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift

variable {B1 B2 : ℕ}

theorem emitOperator_ready (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (token : Tok) :
    Hs C (emitOperator token) a (2*(tokWord token).length+1) (fun b=>
      b.out=a.out++tokWord token ∧ SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b [vJ]) := by
  obtain ⟨b,n,he,hn,bo,bs,bc,bfr⟩:=emitOperator_spec C token a h.constants
  have hf : SourceFrame a b := SourceFrame.of_rest bs bfr (by decide)
  have hv : Valid C b := he.valid (by have hw:=h.width_five; omega)
    (fun s hs=>(wf_out_len C.K.wf s).trans (by omega)) h.valid
  exact ⟨b,n,he,hn,bo,h.of_frame bc hv hf,hf,bfr⟩

theorem finishFermat_ready (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) :
    Hs C finishFermatFactor a (40*sourceBits E+78) (fun b=>
      b.out=a.out++tokWord (.pow (r.prime-1))++tokWord .sub ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b (targetValue::tokenScratch)) := by
  obtain ⟨b,n,he,hn,bo,bs,bc,bfr⟩:=finishFermatFactor_spec C a h.constants r.prime
    (Reconstruct.PrintRequest.prime_prime r).pos h.prime (by have hw:=h.width_five; omega)
    (lt_of_le_of_lt (Nat.add_le_add_right h.prime_bits 2) h.bits_room)
  have hf : SourceFrame a b := SourceFrame.of_rest bs bfr (by decide)
  have hv : Valid C b := he.valid (by have hw:=h.width_five; omega)
    (fun s hs=>(wf_out_len C.K.wf s).trans (by omega)) h.valid
  exact ⟨b,n,he,hn.trans (by have hb:=h.prime_bits; omega),bo,h.of_frame bc hv hf,hf,bfr⟩

end NearQuarticWires.StageLiftTokens
