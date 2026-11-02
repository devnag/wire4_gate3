import Proof.Quartic.StageLift.SourceStateFrame
import Proof.Quartic.StageLift.SourceRuntimeBounds
import Proof.Quartic.StageLift.ResidueCacheContract
import Proof.Quartic.StageCert.FrequencyCounts

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open StageCert.Tokens

/-- Step 3 and `lem:print`, paper/paper.tex: the actual Gamma split is emitted before the original
bank counts are physically restored after register127's phase reuse. -/
def emitWalkHead : St VV MM := .seq emitCurrentGammaWeight loadOccurrenceCounts

/-- Step 3 and `prop:time`, paper/paper.tex: exact source cursors bound the once-per-walk Gamma
selection and original occurrence-count reload. -/
noncomputable def walkHeadCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  70 * (sourceEnvelope r + 1) ^ 2 + 2 * sourceEnvelope r + 545

/-- Step 3 and `lem:print`, paper/paper.tex: actual retained sources produce the original leading
coefficient, advance precisely one Gamma field and restore every
actual residue-body entry field, with no supplied count or coefficient. -/
theorem emitWalkHead_spec {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) (a : DS VV MM)
    (ha : WalkSourceState C r index.val a) (hi : a.env printWalkIndex = index.val)
    (hW : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd) :
    Hs C emitWalkHead a (walkHeadCost r) (fun z =>
      z.out = a.out ++ tokWord (.const
        (Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign (printWalkAt _ index))) ∧
      WalkSourceState C r (index.val + 1) z ∧ ResidueReady C r z (sourceEnvelope r) ∧
      z.env printWalkIndex = index.val ∧ z.ip = a.ip) := by
  have hbds := sourceEnvelope_bounds r
  have hsmall : sourceEnvelope r + 1 ≤ (sourceEnvelope r + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have hbits := source_walk_counter_bits r
  have hcount : r.child.cellCall.seed.N ^ 8 < 2 ^ C.Wd :=
    (lt_natBitLength _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hv := ha.valid (by rw [hi]; exact index.isLt.trans hcount)
  have hindex : a.ram indexStore = normalizedPrintIndex r := ha.sources.indexFields
  have hgamma : a.ram gammaStore =
      (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).map Bool.toNat :=
    ha.sources.gammaBits
  have hcur := hv.rc_le indexStore
  rw [hindex] at hcur
  have hlen : (normalizedPrintIndex r).length = 10 + 2 * r.child.selected.1.J + 2 := by
    simp only [normalizedPrintIndex, List.length_append, List.length_singleton,
      List.length_map, List.length_ofFn, print_digit_count, printResidueList_length, Algorithm.traceOrder]
    omega
  rw [hlen] at hcur
  have hJ := hbds.chains
  have hg := StagePrint.source_addValid (by omega : 1 ≤ C.Wd) hv
    (emitCurrentGammaWeight_spec C r index.val index.isLt a ha.constants hindex hgamma ha.gammaCursor hW)
  obtain ⟨b, nb, heb, hnb, ⟨hbo, hbgamma, hbram, hbrc, hbsh, hbc, hbfr⟩, hbvalid⟩ := hg
  have hbg : b.rc preparedStore = a.rc preparedStore := hbrc _ (by decide) (by decide)
  have hbkin : b.kin = [] :=
    (congrArg (fun t => t.2.1) hbsh).trans ha.inputEmpty
  have hfields : ∀ x ∈ sourceHeaderRegisters, b.env x = a.env x := by
    have hd : ∀ x : Fin VV, x ∈ sourceHeaderRegisters → x ∉ partVar :: gammaTokenScratch := by decide
    intro x hx
    exact hbfr x (hd x hx)
  have hbstate := ha.of_frame hbram hfields hbgamma hbg hbc hbvalid hbkin
  have hparams : b.ram parameterStore = parameterScalars r.child.selected.1 := hbstate.sources.scalarFields
  have hpc := hbvalid.rc_le parameterStore
  rw [hparams, parameterScalars_length] at hpc
  have hs := Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  have hG := hbds.occurrences
  have hfit : r.child.call.first.gates.length + r.child.call.second.gates.length < 2 ^ C.Wd := by
    have hsum : r.child.call.first.gates.length + r.child.call.second.gates.length =
        (Builder.allGates r.child.call).length := by simp only [Builder.allGates, List.length_append]
    rw [hsum]
    have hp : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
    omega
  have hf := StagePrint.source_addValid (by omega : 1 ≤ C.Wd) hbvalid
    (loadOccurrenceCounts_run C r.child.call hs b hbc hparams (by omega) hfit)
  obtain ⟨z, nz, hez, hnz, ⟨hzfirst, hzG, _hzcur, hzrest, hzc, hzfr⟩, hzvalid⟩ := hf
  have hzram : z.ram = b.ram := congrArg (fun t => t.2.2.1) hzrest
  have hzprep : z.rc preparedStore = b.rc preparedStore :=
    (avoidsStore_spec hez (by decide)).2
  have hzgamma : z.rc gammaStore = gammaByteCursor r (index.val + 1) :=
    ((avoidsStore_spec hez (by decide)).2).trans hbgamma
  have hzfields : ∀ x ∈ sourceHeaderRegisters, z.env x = b.env x := by
    have hd : ∀ x : Fin VV, x ∈ sourceHeaderRegisters →
        x ∉ [t2, vJ, c0, atomValue, tupleQuotient, tupleRemainder, firstGateCount, atomCount] := by decide
    intro x hx
    exact hzfr x (hd x hx)
  have hzkin : z.kin = [] :=
    (congrArg (fun t => t.2.2.2.2.1) hzrest).trans hbkin
  have hzstate := hbstate.of_frame hzram hzfields hzgamma hzprep hzc hzvalid hzkin
  have hzG' : z.env atomCount = (Builder.allGates r.child.call).length := by
    simpa only [Builder.allGates, List.length_append] using hzG
  have hzready : ResidueReady C r z (sourceEnvelope r) :=
    ⟨hzc, hzvalid, hzstate.sources.scalarFields, hzstate.sources.factorFields,
      hzstate.sources.witnessBits, hzstate.sources.indexFields, hzstate.sources.exponent,
      hzstate.sources.chains, hzstate.sources.modulus, hzstate.sources.prime,
      hzstate.sources.signs, hzstate.sources.kind, hzG', hzfirst, hbds.positive,
      hbds.occurrences, hbds.exponent, hbds.chains, hbds.partition, hbds.prime,
      hbds.M1, hbds.A, hbds.factors, hbds.witness, hW⟩
  have hzo : z.out = b.out := congrArg (fun t => t.2.1) hzrest
  have hzip : z.ip = b.ip := congrArg (fun t => t.1) hzrest
  have hbip : b.ip = a.ip := congrArg (fun t => t.1) hbsh
  have hzI : z.env printWalkIndex = index.val :=
    (hzfr _ (by decide)).trans ((hbfr _ (by decide)).trans hi)
  refine ⟨z, nb + nz + 1, Ex.seq heb hez, ?_, by rw [hzo]; exact hbo,
    hzstate, hzready, hzI, hzip.trans hbip⟩
  unfold walkHeadCost
  omega

end NearQuarticWires.StageLift
