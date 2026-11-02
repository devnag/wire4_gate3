import Proof.Quartic.StageCertNative.PriceTerms
import Proof.Quartic.StageCertNative.PriceRead
import Proof.Quartic.StageCert.MomentFramedPrice

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCert.Tokens

private theorem maskPower_bound {B1 B2 : ℕ} (r : TermJob B1 B2) (p : ℕ) (hp : p≤16) :
    (((Builder.allGates r.moment.call).length+1)^r.moment.selected.1.Xmax)^p≤
      r.moment.selected.1.Uocc^r.moment.packet.degree := by
  have hbase : (Builder.allGates r.moment.call).length+1≤r.moment.selected.1.Uocc := by
    have hh:=r.moment.source_occurrence_guard
    omega
  rw [←pow_mul]
  refine (Nat.pow_le_pow_left hbase _).trans
    (Nat.pow_le_pow_right (job_occurrence_pos r) ?_)
  change r.moment.selected.1.Xmax*p≤16*r.moment.selected.1.Xmax+8*r.moment.selected.1.k
  have hh:=Nat.mul_le_mul_left r.moment.selected.1.Xmax hp
  omega

theorem price_framedSource (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>r.moment.framedSourceBudget) 1 := by
  refine ⟨framedPriceCoefficient B1 B2,framedPriceExponent B1 B2,fun r=>?_⟩
  exact r.moment.framedSourceBudget_arity.trans
    (Nat.mul_le_mul_left _ (by simpa only [one_mul] using maskPower_bound r 4 (by decide)))

theorem price_packetLength (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>r.moment.packet.word.length+1) 1 := by
  have hpoly:=(JobPrice.constant 1000000).mul ((price_runtimeScale B1 B2).pow 4)
  have hmask : JobPrice (fun r : TermJob B1 B2=>
      ((Builder.allGates r.moment.call).length+1)^r.moment.selected.1.Xmax) 1 := by
    refine ⟨1,0,fun r=>?_⟩
    simpa only [pow_one,pow_zero,one_mul] using maskPower_bound r 1 (by decide)
  exact (hpoly.mul hmask).mono (fun r=>r.moment.packet_length_scale)

theorem price_formatterSteps (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>r.moment.validPacket.steps) 2 := by
  refine ((JobPrice.constant 1000000).mul ((price_packetLength B1 B2).pow 2)).mono ?_
  intro r
  exact StageFormulaMetadata.formatterSteps_le r.moment.validPacket.val
    (NearCubicGates.Close.Interfaces.Formats.toks r.moment.validPacket.formula)
    r.moment.validPacket.source r.moment.validPacket.mode

theorem price_formattedLength (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>r.moment.validPacket.output.length) 2 := by
  refine (price_formatterSteps B1 B2).mono ?_
  intro r
  obtain ⟨b,n,he,hn,ho⟩:=StageFormulaMetadata.formatterProgram_spec
    (StageFormulaMetadata.finiteContext StageRecovery.packetCallee r.moment.packet.word)
    r.moment.validPacket.val
    (NearCubicGates.Close.Interfaces.Formats.toks r.moment.validPacket.formula)
    r.moment.validPacket.source r.moment.validPacket.mode rfl le_rfl
  have hh:=he.out_len
  simp only [a0,List.length_nil,zero_add] at hh
  rw [ho] at hh
  exact hh.trans hn

theorem price_projection (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>projectionBudget r.moment) 4 :=
  (JobPrice.constant (10^8)).mul (((price_formattedLength B1 B2).add
    ((JobPrice.constant 1).raise (by decide : 0≤2))).pow 2)

theorem price_suffixFormula (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>suffixFormulaBudget r.moment) 4 :=
  ((((JobPrice.constant 4).mul (price_framedSource B1 B2)).raise (by decide : 1≤4)).add
    ((JobPrice.constant 4).mul (price_projection B1 B2))).add
    ((JobPrice.constant 12).raise (by decide : 0≤4))

theorem price_suffixTerms (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>suffixTermsBudget r.moment) 4 :=
  (((JobPrice.constant 4).mul (price_suffixFormula B1 B2)).add
    (((JobPrice.constant 4).mul (price_framedExpansion B1 B2)).raise (by decide : 3≤4))).add
    ((JobPrice.constant 12).raise (by decide : 0≤4))

theorem price_jobTerms (B1 B2 : ℕ) :
    JobPrice (@jobTermsBudget B1 B2) 4 :=
  ((((JobPrice.constant 4).mul (price_jobSource B1 B2)).raise (by decide : 0≤4)).add
    ((JobPrice.constant 4).mul (price_suffixTerms B1 B2))).add
    ((JobPrice.constant 12).raise (by decide : 0≤4))

end NearQuarticWires.StageCertNative
