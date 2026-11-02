import Proof.Quartic.StageMain.CompactDecodeSuffix
import Proof.Quartic.StageMain.CompactLayout
import Proof.Quartic.StageLift.CallSource

/-!
# Decoding the actual finite source for the main pass

Step 4 of `sec:algorithm`, paper/paper.tex,
uses the original circuit and witness from `sec:algorithm`. The
physical reader stores the original call and decodes the parameter
and witness words, ending before the first certificate marker.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Compact

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageLift CallSkip

def decodeCompact : St VV MM := .seq readCallSource decodeSuffix

def decodeStores : List (Fin MM) :=
  [parameterStore, primeStore, factorStore, witnessStore, callStore]

def decodeScratch : List (Fin VV) := gateListScratch ++
  [StageRecovery.tokenLengthVar, StageRecovery.inputReturnIndex, c0, t0] ++ decodeSuffixScratch

def decodeCost (c : Call) (p : Cells.Parameters) (witness : List Bool) (B : ℕ) : ℕ :=
  3000 * ((callWord c).length + 1) ^ 3 + 12 * (callWord c).length +
    parameterReadCost p B + 8 * witness.length + 22

structure Decoded (c : Call) (p : Cells.Parameters) (witness : List Bool)
    (a : DS VV MM) : Prop where
  originalCall : a.ram callStore = (callWord c).map Bool.toNat
  scalarFields : a.ram parameterStore = parameterScalars p
  primeFields : a.ram primeStore = p.primes.sort (· ≤ ·)
  factorFields : a.ram factorStore = p.factors
  witnessBits : a.ram witnessStore = witness.map Bool.toNat
  callBytes : a.env lengthCounter = (callWord c).length
  primeCount : a.env primeCountVar = p.primes.card
  factorCount : a.env factorCountVar = p.factors.length

theorem decodeCompact_run (C : Ctx) (c : Call) (p : Cells.Parameters) (B : ℕ)
    (witness rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = compactInput c p witness ++ rest)
    (hcall : (callWord c).length + 2 ≤ C.Wd)
    (hwidth : ∀ value ∈ parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++
      parameterTailFields p ++ p.factors, natBitLength value ≤ B)
    (hB : B + 2 ≤ C.Wd)
    (hcounts : p.primes.card < 2 ^ C.Wd ∧ p.factors.length < 2 ^ C.Wd)
    (hempty : ∀ store ∈ decodeStores, a.ram store = [] ∧ a.rc store = 0) :
    Hs C decodeCompact a (decodeCost c p witness B) (fun b =>
      b.ip = a.ip + (compactInput c p witness).length ∧ Decoded c p witness b ∧
      (∀ store, store ∉ decodeStores → b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b decodeScratch) := by
  have hinput : C.inp.drop a.ip = true :: (callWord c ++ (Program.parametersWord p ++ frame witness ++ rest)) := by
    simpa only [compactInput, preparedPrefixWord, List.cons_append, List.append_assoc] using hin
  unfold decodeCompact
  refine (Hs.seq (t2 := parameterReadCost p B + 8 * witness.length + 5)
    (readCallSource_spec C c (Program.parametersWord p ++ frame witness ++ rest) a hc hinput
      hcall (hempty _ (by simp [decodeStores]))) ?_).mono
      (by unfold decodeCost; omega) (fun _ h => h)
  rintro b ⟨hbip, hblen, hbcall, _hbcallc, hbother, hbrest, hbc, hbfr⟩
  have hbin : C.inp.drop b.ip = Program.parametersWord p ++ frame witness ++ rest := by
    rw [hbip, show a.ip + 1 + (callWord c).length = a.ip + ((callWord c).length + 1) by omega,
      ← List.drop_drop, hinput]
    simp only [List.drop_succ_cons, List.drop_left]
  have hbempty : ∀ store ∈ [parameterStore, primeStore, factorStore, witnessStore],
      b.ram store = [] ∧ b.rc store = 0 := by
    intro store hs
    have hne : store ≠ callStore := by
      rcases (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hs) with
        hs | hs | hs | hs <;> subst store <;> decide
    obtain ⟨hr, hrc⟩ := hbother store hne
    rw [hr, hrc]
    exact hempty store (by simp only [decodeStores, List.mem_cons] at hs ⊢; tauto)
  refine (decodeSuffix_run C p B witness rest b hbc hbin hwidth hB hcounts hbempty).mono le_rfl ?_
  rintro d ⟨hdip, hdpar, hdprime, hdfactor, hdwit, _hdpc, _hdprc, _hdfc, _hdwc,
    hdpn, hdfn, hdother, hdrest, hdc, hdfr⟩
  refine ⟨?_, ⟨?_, hdpar, hdprime, hdfactor, hdwit, ?_, hdpn, hdfn⟩, ?_,
    hdrest.trans hbrest, hdc, ?_⟩
  · rw [hdip, hbip]
    simp only [compactInput, preparedPrefixWord, List.length_cons, List.length_append]
    omega
  · rw [(hdother callStore (by decide)).1, hbcall]
  · rw [hdfr lengthCounter (by decide), hblen]
  · intro store hs
    have hsmall : store ∉ [parameterStore, primeStore, factorStore, witnessStore] := by
      simp only [decodeStores, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs ⊢
      tauto
    have hcall' : store ≠ callStore := fun heq => hs (by simp [decodeStores, heq])
    obtain ⟨hr₁, hc₁⟩ := hdother store hsmall
    obtain ⟨hr₂, hc₂⟩ := hbother store hcall'
    exact ⟨hr₁.trans hr₂, hc₁.trans hc₂⟩
  · exact (hbfr.weaken (fun _ hx => List.mem_append_left _ hx)).trans
      (hdfr.weaken (fun _ hx => List.mem_append_right _ hx))

end NearQuarticWires.StageMain.Compact
