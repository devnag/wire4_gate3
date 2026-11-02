import Proof.Quartic.StageLift.ParameterRun
import Proof.Quartic.StageLift.PrintFrames
import Proof.Quartic.StageLift.StoreFrame

/-!
# Reading the parameters and witness for Step 4

`sec:algorithm`, paper/paper.tex:
the selected parameters and the original framed witness are decoded
from the source before traversing the certified columns. The following
certificate and seed suffix is left unread.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Compact

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageLift

def decodeSuffix : St VV MM := .seq readParameters (readFrame witnessStore)

def decodeSuffixScratch : List (Fin VV) := primeCountVar :: factorCountVar :: fieldIndex :: rdNatT

theorem decodeSuffix_run (C : Ctx) (p : Cells.Parameters) (B : ℕ)
    (witness rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = Program.parametersWord p ++ frame witness ++ rest)
    (hwidth : ∀ value ∈ parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++
      parameterTailFields p ++ p.factors, natBitLength value ≤ B)
    (hB : B + 2 ≤ C.Wd)
    (hcounts : p.primes.card < 2 ^ C.Wd ∧ p.factors.length < 2 ^ C.Wd)
    (hempty : ∀ store ∈ [parameterStore, primeStore, factorStore, witnessStore],
      a.ram store = [] ∧ a.rc store = 0) :
    Hs C decodeSuffix a (parameterReadCost p B + 8 * witness.length + 5) (fun b =>
      b.ip = a.ip + (Program.parametersWord p).length + (frame witness).length ∧
      b.ram parameterStore = parameterScalars p ∧
      b.ram primeStore = p.primes.sort (· ≤ ·) ∧ b.ram factorStore = p.factors ∧
      b.ram witnessStore = witness.map Bool.toNat ∧
      b.rc parameterStore = 46 ∧ b.rc primeStore = p.primes.card ∧
      b.rc factorStore = p.factors.length ∧ b.rc witnessStore = witness.length ∧
      b.env primeCountVar = p.primes.card ∧ b.env factorCountVar = p.factors.length ∧
      (∀ store, store ∉ [parameterStore, primeStore, factorStore, witnessStore] →
        b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b decodeSuffixScratch) := by
  obtain ⟨b, n, he, hn, hb⟩ := readParameters_cursor_spec C p B (frame witness ++ rest) a hc
    (by simpa only [List.append_assoc] using hin) hwidth hB hcounts
    (by intro store hs; exact hempty store (by simp only [List.mem_cons] at hs ⊢; tauto))
  have hbother : ∀ store, store ∉ [parameterStore, primeStore, factorStore] →
      b.ram store = a.ram store ∧ b.rc store = a.rc store :=
    fun store hs => avoidsStore_spec he (readParameters_avoids store hs)
  rcases hb with ⟨⟨hbi, hbp, hbpr, hbf, hbpn, hbfn, hbsh, hbc, hbfr⟩, hbpc, hbprc, hbfc⟩
  have hbin : C.inp.drop b.ip = frame witness ++ rest := by
    rw [hbi, ← List.drop_drop, hin, List.append_assoc, List.drop_left]
  have hbw : b.ram witnessStore = [] ∧ b.rc witnessStore = 0 := by
    obtain ⟨hr, hrc⟩ := hbother witnessStore (by decide)
    rw [hr, hrc]
    exact hempty witnessStore (by simp)
  unfold decodeSuffix
  refine (Hs.seq (t1 := parameterReadCost p B) (t2 := 8 * witness.length + 4)
    (show Hs C readParameters a (parameterReadCost p B) (· = b) from ⟨b, n, he, hn, rfl⟩) ?_).mono
    (by omega) (fun _ h => h)
  intro e heq
  subst e
  refine (readFrame_spec C witnessStore witness rest b hbc hbin
    (by rw [hbw.1, hbw.2]; rfl)).mono le_rfl ?_
  rintro d ⟨hdi, hdr, hdrc, hdo, hdsh, hdc, hdfr⟩
  refine ⟨by rw [hdi, hbi], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hdsh.trans hbsh, hdc, hbfr.trans (hdfr.weaken (by decide))⟩
  · rw [(hdo _ (by decide)).1, hbp]
  · rw [(hdo _ (by decide)).1, hbpr]
  · rw [(hdo _ (by decide)).1, hbf]
  · rw [hdr, hbw.1]; rfl
  · rw [(hdo _ (by decide)).2, hbpc]
  · rw [(hdo _ (by decide)).2, hbprc]
  · rw [(hdo _ (by decide)).2, hbfc]
  · rw [hdrc, hbw.2]; omega
  · rw [hdfr _ (by decide), hbpn]
  · rw [hdfr _ (by decide), hbfn]
  · intro store hs
    have hs' : store ∉ [parameterStore, primeStore, factorStore] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hs ⊢
      tauto
    have hsw : store ≠ witnessStore := fun heq => hs (by simp [heq])
    obtain ⟨hr₁, hc₁⟩ := hdo store hsw
    obtain ⟨hr₂, hc₂⟩ := hbother store hs'
    exact ⟨hr₁.trans hr₂, hc₁.trans hc₂⟩

end NearQuarticWires.StageMain.Compact
