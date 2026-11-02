import Proof.Quartic.StageLift.ParameterRun
import Proof.Quartic.StageLift.PrintFrames
import Proof.Quartic.StageLift.StoreFrame

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `lem:print` and Step 3, paper/paper.tex: after locating the real call endpoint, read and retain the
actual parameter record, witness frame and Gamma frame exactly once. -/
def readPrintSuffix : St VV MM := .seq readParameters readPrintFrames

/-- `lem:print` and Step 3, paper/paper.tex: the literal print source is decoded into actual stores,
ending at its unchanged index suffix and preserving any finite call copy. -/
theorem readPrintSuffix_spec (C : Ctx) (p : Cells.Parameters) (B : ℕ)
    (witness gamma rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = Program.parametersWord p ++
      frame witness ++ frame gamma ++ rest)
    (hwidth : ∀ value ∈ parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++
      parameterTailFields p ++ p.factors, natBitLength value ≤ B)
    (hB : B + 2 ≤ C.Wd)
    (hcounts : p.primes.card < 2 ^ C.Wd ∧ p.factors.length < 2 ^ C.Wd)
    (hempty : ∀ store ∈ [parameterStore, primeStore, factorStore, witnessStore, gammaStore],
      a.ram store = [] ∧ a.rc store = 0) :
    Hs C readPrintSuffix a
      (parameterReadCost p B + 8 * witness.length + 8 * gamma.length + 10) (fun b =>
      b.ip = a.ip + (Program.parametersWord p).length +
        (frame witness).length + (frame gamma).length ∧
      b.ram parameterStore = parameterScalars p ∧
      b.ram primeStore = p.primes.sort (· ≤ ·) ∧ b.ram factorStore = p.factors ∧
      b.rc parameterStore = 46 ∧ b.rc primeStore = p.primes.card ∧
      b.rc factorStore = p.factors.length ∧
      b.ram witnessStore = witness.map Bool.toNat ∧ b.ram gammaStore = gamma.map Bool.toNat ∧
      b.rc witnessStore = witness.length ∧ b.rc gammaStore = gamma.length ∧
      b.env primeCountVar = p.primes.card ∧ b.env factorCountVar = p.factors.length ∧
      (∀ store, store ∉ [parameterStore, primeStore, factorStore, witnessStore, gammaStore] →
        b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (primeCountVar :: factorCountVar :: fieldIndex :: rdNatT)) := by
  obtain ⟨b, n, he, hn, hb⟩ := readParameters_cursor_spec C p B
    (frame witness ++ frame gamma ++ rest) a hc
    (by simpa only [List.append_assoc] using hin) hwidth hB hcounts
    (by intro store hs; exact hempty store (by simp only [List.mem_cons] at hs ⊢; tauto))
  have hbother : ∀ store, store ∉ [parameterStore, primeStore, factorStore] →
      b.ram store = a.ram store ∧ b.rc store = a.rc store := by
    intro store hs
    exact avoidsStore_spec he (readParameters_avoids store hs)
  rcases hb with ⟨⟨hbi, hbp, hbpr, hbfac, hbpn, hbfn, hbsh, hbc, hbfr⟩, hbpc, hbprc, hbfc⟩
  have hbin : C.inp.drop b.ip = frame witness ++ frame gamma ++ rest := by
    rw [hbi, ← List.drop_drop, hin, List.append_assoc, List.append_assoc, List.drop_left]
    simp only [List.append_assoc]
  have hbempty : b.ram witnessStore = [] ∧ b.rc witnessStore = 0 ∧
      b.ram gammaStore = [] ∧ b.rc gammaStore = 0 := by
    obtain ⟨hwr, hwc⟩ := hbother witnessStore (by decide)
    obtain ⟨hgr, hgc⟩ := hbother gammaStore (by decide)
    rw [hwr, hwc, hgr, hgc]
    exact ⟨(hempty _ (by simp)).1, (hempty _ (by simp)).2, hempty _ (by simp)⟩
  unfold readPrintSuffix
  refine (Hs.seq (t1 := parameterReadCost p B)
    (t2 := 8 * witness.length + 8 * gamma.length + 9)
    (show Hs C readParameters a (parameterReadCost p B) (· = b) from
      ⟨b, n, he, hn, rfl⟩) fun e heq => ?_).mono (by omega) (fun _ h => h)
  subst e
  refine (readPrintFrames_spec C witness gamma rest b hbc hbin hbempty).mono le_rfl ?_
  rintro d ⟨hdi, hdw, hdg, hdwc, hdgc, hdother, hdsh, hdc, hdfr⟩
  refine ⟨by rw [hdi, hbi], ?_, ?_, ?_, ?_, ?_, ?_, hdw, hdg, hdwc, hdgc,
    ?_, ?_, ?_, hdsh.trans hbsh, hdc, ?_⟩
  · rw [(hdother _ (by decide) (by decide)).1, hbp]
  · rw [(hdother _ (by decide) (by decide)).1, hbpr]
  · rw [(hdother _ (by decide) (by decide)).1, hbfac]
  · rw [(hdother _ (by decide) (by decide)).2, hbpc]
  · rw [(hdother _ (by decide) (by decide)).2, hbprc]
  · rw [(hdother _ (by decide) (by decide)).2, hbfc]
  · rw [hdfr _ (by decide), hbpn]
  · rw [hdfr _ (by decide), hbfn]
  · intro store hs
    have hs' : store ∉ [parameterStore, primeStore, factorStore] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hs ⊢
      tauto
    have hsw : store ≠ witnessStore := by
      intro heq
      exact hs (by simp [heq])
    have hsg : store ≠ gammaStore := by
      intro heq
      exact hs (by simp [heq])
    obtain ⟨hdr, hdrc⟩ := hdother store hsw hsg
    obtain ⟨hbr, hbrc⟩ := hbother store hs'
    exact ⟨hdr.trans hbr, hdrc.trans hbrc⟩
  · exact hbfr.trans (hdfr.weaken (by decide))

end NearQuarticWires.StageLift
