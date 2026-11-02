import Proof.Quartic.StageLiftTokens.TokenRun
import Proof.Quartic.StageLift.AmplifierCoefficient

/-!
# Actual BT coefficients and power tokens

`imp:amp` and `lem:print`, paper/paper.tex: powers use the live exponent register, and each integer
binomial coefficient is computed by the original exact multiply/divide
recurrence before any normalization modulo the composite modulus.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats StageLift StageCert.Tokens

variable {B1 B2 : ℕ}

def emitPower (value : Fin VV) : St VV MM := emitPrefixedVariable (natWord 6) value

theorem emitPower_ready (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (value : Fin VV) (hx : value≠t3) (hJ : value≠vJ)
    (hv : a.env value≤E) :
    Hs C (emitPower value) a (40*sourceBits E+58) (fun b=>
      b.out=a.out++tokWord (.pow (a.env value)) ∧ SourceReady C r b E ∧
      SourceFrame a b ∧ Fr a b tokenScratch) := by
  have hb : natBitLength (a.env value)≤ sourceBits E := by
    apply source_small_bits E _ h.envelope_pos
    have hp:=Nat.le_self_pow (by decide : 3≠0) (E+1)
    omega
  obtain ⟨b,n,he,hn,bo,bs,bc,bfr⟩:=emitPrefixedVariable_spec C (natWord 6) value hx hJ a h.constants
    (by have hh:=h.width_five; omega) (lt_of_le_of_lt (Nat.add_le_add_right hb 2) h.bits_room)
  have hf : SourceFrame a b := SourceFrame.of_rest bs bfr (by decide)
  have hvalid : Valid C b := he.valid (by have hw:=h.width_five; omega)
    (fun s hs=>(wf_out_len C.K.wf s).trans (by omega)) h.valid
  refine ⟨b,n,he,hn.trans ?_,?_,h.of_frame bc hvalid hf,hf,bfr⟩
  · have hl : (natWord 6).length=7 := by decide
    rw [hl]
    omega
  · simpa only [tokWord,List.append_assoc] using bo

def amplifierCoefficientScratch : List (Fin VV) :=
  chooseN::chooseR::(binomialScratch++tokenScratch)

theorem emitCoefficient_ready (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (j : Fin r.child.selected.1.e)
    (hj : a.env amplifierIndex=j.val) :
    Hs C emitAmplifierCoefficient a (17*j.val+40*sourceBits E+82) (fun b=>
      b.out=a.out++tokWord (.const (((r.child.selected.1.e-1+j.val).choose j.val:ℕ):ℤ)) ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b amplifierCoefficientScratch) := by
  obtain ⟨b,n,he,hn,bo,_bv,bs,bc,bfr⟩:=emitAmplifierCoefficient_spec C a h.constants
    r.child.selected.1.e j.val (sourceBits E)
    (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2).e_pos j.isLt h.exponent hj
    (source_binomial_capacity E C.Wd _ h.envelope_pos h.width h.exponent_bound)
    (by have hw:=h.width_five; omega)
    (source_binomial_bits E _ _ h.envelope_pos h.exponent_bound j.isLt) h.bits_room
  have hf : SourceFrame a b := SourceFrame.of_rest bs bfr (by decide)
  have hv : Valid C b := he.valid (by have hw:=h.width_five; omega)
    (fun s hs=>(wf_out_len C.K.wf s).trans (by omega)) h.valid
  exact ⟨b,n,he,hn,bo,h.of_frame bc hv hf,hf,bfr⟩

end NearQuarticWires.StageLiftTokens
