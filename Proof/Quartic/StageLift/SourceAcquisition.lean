import Proof.Quartic.StageLift.SourceRuntimeBounds
import Proof.Quartic.StageLift.SourceIndexBounds
import Proof.Quartic.StageMain.CompactBounds

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- Step 3 and `prop:time`, paper/paper.tex: the once-paid acquisition clock uses the original
small preparation size and the actual raw index-word length. -/
noncomputable def sourceAcquisitionCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (markerCursor : ℕ) : ℕ :=
  cachedRequestCost r (preparedWordOf r).length (Greedy.printIndexWord r).length markerCursor

/-- `lem:print`, Step 3 and `prop:time`, paper/paper.tex: the literal original printer input
supplies every retained source and normalized index, with all parser
preconditions derived from its existing selected-parameter proofs.
Raw target magnitudes contribute only to the once-paid clock. -/
theorem acquireSelectedPrintSource_spec {B1 B2 : ℕ} (C : Ctx)
    (r : Greedy.PrintRequest B1 B2) (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = Greedy.printInput r ++ rest)
    (hW : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd)
    (hempty : ∀ store ∈ [parameterStore, primeStore, factorStore, witnessStore,
      gammaStore, callStore, indexStore, preparedStore], a.ram store = [] ∧ a.rc store = 0) :
    Hs C readCachedPrintRequest a (sourceAcquisitionCost r (a.rc indexMarkerStore)) (fun b =>
      PrintRequestData r b ∧ b.ram preparedStore = (preparedWordOf r).map Bool.toNat ∧
      b.env preparedLength = (preparedWordOf r).length ∧ b.rc preparedStore = (preparedWordOf r).length ∧
      C.inp.drop b.ip = rest ∧
      b.rc indexMarkerStore ≤ a.rc indexMarkerStore + 2 * (Greedy.printIndexWord r).length + 2 ∧
      (∀ store, store ∉ [parameterStore, primeStore, factorStore, witnessStore,
        gammaStore, callStore, indexStore, indexMarkerStore, preparedStore] →
        b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b) := by
  have hb := sourceEnvelope_bounds r
  have hprimeBound := hb.prime
  have hsmall : sourceEnvelope r + 1 ≤ (sourceEnvelope r + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have hP : (preparedWordOf r).length + 2 ≤ C.Wd := by
    have hp : (preparedWordOf r).length ≤ sourceEnvelope r := by dsimp [sourceEnvelope]; omega
    omega
  obtain ⟨hprepared, hcap, hbits, hprimes, hfactors⟩ :=
    StageMain.Compact.compact_decoder_bounds r.child.call r.child.selected.1
      (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness) C.Wd hP
  have hpbits := nbl_le_self r.prime
  obtain ⟨hcountWidths, hcountFits⟩ := source_index_counter_bounds C r hW
  exact readCachedPrintRequest_spec C r (preparedWordOf r).length (Greedy.printIndexWord r).length
    rest a hc hin hprepared hcap hbits hP ⟨hprimes, hfactors⟩ hempty (by omega)
    (by omega) (source_modulus_fits C r hW) (raw_print_index_bits r) hcountWidths hcountFits

end NearQuarticWires.StageLift
