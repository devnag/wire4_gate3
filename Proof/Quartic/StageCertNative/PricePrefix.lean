import Proof.Quartic.StageCertNative.PriceFormatted
import Proof.Quartic.StageCertNative.PrefixMachine
import Proof.Quartic.StageMain.CompilerRuntime

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCert.Tokens

theorem price_arity (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>r.moment.call.n) 0 :=
  JobPrice.of_arity ⟨1,1,by intro r;simp⟩

theorem JobPrice.natBits {B1 B2 : ℕ} {f : TermJob B1 B2→ℕ} {d : ℕ}
    (h : JobPrice f d) : JobPrice (fun r=>natBitLength (f r)) d :=
  (h.add ((JobPrice.constant 1).raise (Nat.zero_le d))).mono
    (fun r=>NearCubicGates.Close.Dispatch.natBitLength_le_succ (f r))

theorem JobPrice.natWordLength {B1 B2 : ℕ} {f : TermJob B1 B2→ℕ} {d : ℕ}
    (h : JobPrice f d) : JobPrice (fun r=>(natWord (f r)).length) d := by
  have h2 : JobPrice (fun r=>2*natBitLength (f r)) d := by
    simpa only [zero_add] using (JobPrice.constant 2).mul h.natBits
  have hh:=h2.add ((JobPrice.constant 1).raise (Nat.zero_le d))
  simpa only [natWord_length] using hh

theorem price_nFirstLength (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(nFirstWord r).length) 0 :=
  JobPrice.of_arity ⟨sharedSourceCoefficient B1 B2,sharedSourceExponent B1 B2,
    nFirstWord_length_arity⟩

theorem price_contextLength (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(StagePrint.Context.word r.base.prepared).length) 0 := by
  refine (price_wordLength B1 B2).mono ?_
  intro r
  rw [r.word_layout,List.length_append]
  omega

theorem price_prefixCapacity (B1 B2 : ℕ) : JobPrice (@prefixCapacity B1 B2) 0 :=
  JobPrice.of_arity ⟨prefixCapacityCoefficient B1 B2,prefixCapacityExponent B1 B2,
    prefixCapacity_arity⟩

theorem price_prefixScalarBits (B1 B2 : ℕ) : JobPrice (@prefixScalarBits B1 B2) 0 :=
  (price_prefixCapacity B1 B2).mono (fun r=>by unfold prefixCapacity;omega)

theorem price_prefixSteps (B1 B2 : ℕ) : JobPrice (@prefixProgramSteps B1 B2) 0 := by
  have hread:=(((JobPrice.constant 30).mul (price_arity B1 B2).natBits).add
    (JobPrice.constant 33)).add (price_countedRead B1 B2)
  have hmeta:=(((hread.add (price_wordLength B1 B2)).add
    ((JobPrice.constant 30).mul (price_arity B1 B2).natBits)).add
    (JobPrice.constant (nativeBitsSteps B1))).add (JobPrice.constant 500)
  have hout:=(((JobPrice.constant 11).mul (price_contextLength B1 B2)).add
    ((JobPrice.constant 160).mul (price_prefixScalarBits B1 B2))).add (JobPrice.constant 300)
  exact ((JobPrice.constant 3).mul ((hmeta.add hout).add (JobPrice.constant 1))).add
    (JobPrice.constant 8)

private noncomputable def prefixCompilerScale {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  (prefixSizes B1 B2).W (natBitLength r.moment.call.n)+natBitLength r.moment.call.n+
    10*(prefixCapacityCoefficient B1 B2+1)+(prefixCapacityExponent B1 B2+2)+VV+MM+100

private theorem price_prefixCompilerScale (B1 B2 : ℕ) :
    JobPrice (@prefixCompilerScale B1 B2) 0 := by
  have hw : JobPrice (fun r : TermJob B1 B2=>
      (prefixSizes B1 B2).W (natBitLength r.moment.call.n)) 0 :=
    JobPrice.of_arity ⟨10*(prefixCapacityCoefficient B1 B2+1)*
        2^(prefixCapacityExponent B1 B2+2),prefixCapacityExponent B1 B2+2,
      fun r=>StageEntryAllocation.width_polynomial _ _ _⟩
  exact (((((hw.add (price_arity B1 B2).natBits).add
    (JobPrice.constant (10*(prefixCapacityCoefficient B1 B2+1)))).add
    (JobPrice.constant (prefixCapacityExponent B1 B2+2))).add
    (JobPrice.constant VV)).add (JobPrice.constant MM)).add (JobPrice.constant 100)

theorem price_prefixBudget (B1 B2 : ℕ) : JobPrice (@prefixBudget B1 B2) 0 := by
  have hs:=((price_prefixSteps B1 B2).add (price_nFirstLength B1 B2)).add
    (JobPrice.constant 1)
  have hp:=((JobPrice.constant 10000).mul ((price_prefixCompilerScale B1 B2).pow 2)).mul hs
  refine hp.mono ?_
  intro r
  have hh : leadOnes (nFirstWord r)=natBitLength r.moment.call.n := by
    unfold nFirstWord
    exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _
  apply StageMain.Runtime.langBudget_le _ _ _ _ _ _ (prefixCompilerScale r)
  all_goals first
    | (rw [hh];unfold prefixCompilerScale;omega)
    | (unfold prefixCompilerScale;omega)
    | (change 3≤prefixCompilerScale r;unfold prefixCompilerScale;omega)
    | (change 10*(prefixCapacityCoefficient B1 B2+1)≤prefixCompilerScale r
       unfold prefixCompilerScale;omega)
    | (change prefixCapacityExponent B1 B2+2≤prefixCompilerScale r
       unfold prefixCompilerScale;omega)
    | (change 0≤prefixCompilerScale r;omega)

theorem price_jobArity (B1 B2 : ℕ) : JobPrice (@jobArityBudget B1 B2) 0 := by
  have hs:=((price_countedRead B1 B2).add ((JobPrice.constant 100).mul
    ((price_wordLength B1 B2).add (JobPrice.constant 1)))).add (JobPrice.constant 100)
  exact (price_wordLength B1 B2).finite
    (((JobPrice.constant 3).mul hs).add (JobPrice.constant 8))
    StageRecovery.packetCallee VV MM

theorem price_nFirstSource (B1 B2 : ℕ) : JobPrice (@nFirstSourceBudget B1 B2) 0 := by
  have hid:=(JobPrice.constant (10^8)).mul
    (((price_wordLength B1 B2).add (JobPrice.constant 1)).pow 2)
  have hio:=((((price_wordLength B1 B2).add (price_arity B1 B2).natWordLength).add
    (price_wordLength B1 B2)).add (JobPrice.constant 1))
  exact ((JobPrice.constant 2).mul
    ((((JobPrice.constant 2).mul (price_jobArity B1 B2)).add
      ((JobPrice.constant 2).mul hid)).add ((JobPrice.constant 300).mul hio))).add
    (JobPrice.constant 2)

theorem price_nFirstNestedTerms (B1 B2 : ℕ) : JobPrice (@nFirstNestedTermsBudget B1 B2) 4 := by
  have hp:=(JobPrice.constant (10^8)).mul
    (((price_nFirstLength B1 B2).add (JobPrice.constant 1)).pow 2)
  have hn:=(((JobPrice.constant 4).mul (price_jobTerms B1 B2)).add
    (((JobPrice.constant 4).mul (((JobPrice.constant 2000).mul
      ((price_termsWord B1 B2).add ((JobPrice.constant 1).raise (by decide : 0≤1)))).add
      ((JobPrice.constant 2).raise (by decide : 0≤1)))).raise (by decide : 1≤4))).add
    ((JobPrice.constant 12).raise (by decide : 0≤4))
  exact ((((JobPrice.constant 4).mul hp).raise (by decide : 0≤4)).add
    ((JobPrice.constant 4).mul hn)).add ((JobPrice.constant 12).raise (by decide : 0≤4))

end NearQuarticWires.StageCertNative
