import Proof.Quartic.StageCertNative.PoolCostTarget
import Proof.Quartic.StageCertNative.PriceFinite
import Proof.Quartic.StageCertNative.PriceLanguage
import Proof.Quartic.StageCertNative.PricePair

set_option autoImplicit false

namespace NearQuarticWires.StageCertNativePoolCost

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCertNative StageCert.Tokens StageCertificateControl

/-- `prop:time`, paper/paper.tex: the
literal original BASE is part of every actual internal source. -/
theorem price_baseWordLength (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>j.base.baseWord.length) 0 := by
  refine (price_wordLength B1 B2).mono ?_
  intro j
  unfold TermJob.word cachedSourceWord
  simp only [List.length_append]
  omega

/-- `prop:time`, paper/paper.tex: the
once-counted and retained actual context is polynomial before any
population or closed-walk term is evaluated. -/
theorem price_cachedSourceLength (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>(cachedSourceWord j.base).length) 0 := by
  refine (price_wordLength B1 B2).mono ?_
  intro j
  unfold TermJob.word
  rw [List.length_append]
  omega

theorem price_prepLength (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>j.base.prepared.word.length) 0 := by
  refine (price_wordLength B1 B2).mono ?_
  intro j
  have hh:=j.moment.prep_length_le
  have he:=actualMoment_word j.base j.index
  change j.moment.word=j.base.baseWord++natWord j.index.val at he
  rw [he,List.length_append] at hh
  change j.base.prepared.word.length≤_ at hh
  unfold TermJob.word cachedSourceWord
  simp only [List.length_append]
  omega

theorem price_contextLength (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>(StagePrint.Context.word j.base.prepared).length) 0 := by
  refine (price_wordLength B1 B2).mono ?_
  intro j
  unfold TermJob.word cachedSourceWord
  simp only [List.length_append]
  omega

theorem price_countBits (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>natBitLength (termCount j.base)) 0 := by
  refine JobPrice.of_arity ⟨5,1,fun j=>?_⟩
  have hh:=count_bits j.base
  have hk:=j.moment.rules.k_lt_n
  change j.base.prepared.selected.1.k<j.moment.call.n at hk
  simpa only [pow_one] using (by omega : natBitLength (termCount j.base)≤5*(j.moment.call.n+1))

theorem price_countWordLength (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>(natWord (termCount j.base)).length) 0 := by
  simpa only [natWord_length] using
    ((JobPrice.constant 2).mul (price_countBits B1 B2)).add (JobPrice.constant 1)

theorem price_zeroMomentLength (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>(zeroMoment j.base).word.length) 0 := by
  have hh:=(price_baseWordLength B1 B2).add (JobPrice.constant (natWord 0).length)
  refine hh.mono ?_
  intro j
  rw [zeroMoment_word,List.length_append]

/-- `prop:time`, paper/paper.tex: all
first-term compiler dimensions and real source reads retain the
same fixed original-arity polynomial, uniformly over all witnesses. -/
theorem price_zeroRuntime (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>(zeroMoment j.base).runtimeScale) 0 := by
  exact JobPrice.of_arity ⟨momentRuntimeCoefficient B1 B2,momentRuntimeExponent B1 B2,
    fun j=>(zeroMoment j.base).runtimeScale_arity⟩

theorem price_zeroReadSteps (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>(zeroMoment j.base).readSteps) 0 := by
  refine ((JobPrice.constant 110000).mul ((price_zeroRuntime B1 B2).pow 3)).mono ?_
  exact fun j=>(zeroMoment j.base).readSteps_le

theorem price_zeroOrdinalBudget (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>zeroOrdinalBudget j.base) 0 :=
  (price_baseWordLength B1 B2).finite (JobPrice.constant 30) StageRecovery.packetCallee VV MM

theorem price_zeroPrepCopyBudget (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>prepCopyBudget (zeroMoment j.base)) 0 := by
  have hprep:=((price_zeroRuntime B1 B2).mono (fun j=>
    (zeroMoment j.base).prep_length_le.trans (zeroMoment j.base).runtimeScale_basic.2.2))
  have hs:=((price_zeroReadSteps B1 B2).add ((JobPrice.constant 9).mul hprep)).add (JobPrice.constant 7)
  exact (price_zeroMomentLength B1 B2).finite
    (((JobPrice.constant 3).mul hs).add (JobPrice.constant 8)) StageRecovery.packetCallee VV MM

theorem price_countBodyBudget (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>countBodyBudget j.base) 0 := by
  have hk : JobPrice (fun j : TermJob B1 B2=>j.base.prepared.selected.1.k) 0 :=
    (price_zeroRuntime B1 B2).mono (fun j=>by
      dsimp only [MomentRequest.runtimeScale,MomentRequest.bodyScale,zeroMoment,actualMoment]
      omega)
  have hs:=((price_zeroReadSteps B1 B2).add
    ((JobPrice.constant 40).mul (((JobPrice.constant 4).mul hk).add (JobPrice.constant 1)))).add
    (JobPrice.constant 100)
  have hR:=price_zeroRuntime B1 B2
  apply (price_zeroMomentLength B1 B2).language
    (((JobPrice.constant 3).mul hs).add (JobPrice.constant 8))
    StageRecovery.packetCallee (momentSourceSizes B1 B2) VV MM
  · refine hR.mono ?_
    intro j
    have hh:=(zeroMoment j.base).source_header []
    simp only [List.append_nil] at hh
    rw [hh]
    have hb:=NearCubicGates.Close.Dispatch.natBitLength_le_succ (zeroMoment j.base).call.n
    dsimp only [MomentRequest.runtimeScale]
    omega
  all_goals
    refine hR.mono ?_
    intro j
    have hh:=(zeroMoment j.base).source_header []
    simp only [List.append_nil] at hh
    rw [hh]
    dsimp only [MomentRequest.runtimeScale]
    omega

end NearQuarticWires.StageCertNativePoolCost
