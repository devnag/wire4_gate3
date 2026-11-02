import Proof.Quartic.StageLift.StreamLoop
import Proof.Quartic.StageLift.StreamInitialize
import Proof.Gates.CounterMachine.PrefixMac

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearQuarticWires.StageRecovery
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)

/-- `lem:print` and `lem:residue`, paper/paper.tex: consume the original natural-word length into markers,
then replay exactly those markers while reducing the actual payload bits. -/
def readNaturalMod (store : Fin MM) : St VV MM :=
  .seq (readUnaryMarkers store) (.seq (initializeStreamPayload store)
    (.loop (.eq t0 v1) (streamPayloadBody store)))

/-- `lem:print` and `lem:residue`, paper/paper.tex: an arbitrarily large original integer magnitude is
reduced directly from its literal bytes, without a bound on its raw
bit length or value in any arithmetic register. The real sentinel is
read and all marker-store rewinds are paid in the linear source cost. -/
theorem readNaturalMod_spec (C : Ctx) (store : Fin MM) (n : ℕ) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a) (q : ℕ) (hq : 2 ≤ q)
    (haq : a.env modulusVar = q) (hfit : 2 * q ≤ 2 ^ C.Wd)
    (hin : C.inp.drop a.ip = natWord n ++ rest) :
    Hs C (readNaturalMod store) a (a.rc store + 30 * natBitLength n + 40) (fun b =>
      b.env leftVar = n % q ∧ b.ip = a.ip + (natWord n).length ∧
      b.ram store = wr (a.ram store) 0 (List.replicate (natBitLength n) 1 ++ [0]) ∧
      b.rc store = natBitLength n + 1 ∧
      (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b payloadBodyScratch) := by
  let L := natBitLength n
  have hinput : C.inp.drop a.ip = (List.replicate L true ++ [false]) ++
      (binary L n ++ rest) := by
    rw [hin, NearCubicGates.Close.CounterMachine.PrefixProg.natWord_bin]
    simp only [L, List.append_assoc, List.cons_append, List.nil_append]
  unfold readNaturalMod
  refine (Hs.seq (t1 := a.rc store + 5 * L + 9) (t2 := 21 * L + 12)
    (readUnaryMarkers_spec C store L (binary L n ++ rest) a hc hinput)
    fun b ⟨hbi, hbr, hbrc, hbo, hbsh, hbc, hbf⟩ => ?_).mono
      (by dsimp only [L]; omega) (fun _ h => h)
  have hbin : C.inp.drop b.ip = binary L n ++ rest := by
    rw [hbi, show a.ip + L + 1 = a.ip + (List.replicate L true ++ [false]).length by simp; omega,
      ← List.drop_drop, hinput, List.drop_left]
  have hbq : b.env modulusVar = q := by rw [hbf _ (by decide)]; exact haq
  have hi := initializeStreamPayload_spec C store L (a.ram store) b hbc hbr
  rw [hbrc] at hi
  refine (Hs.seq (t1 := L + 8) (t2 := 20 * L + 2)
    (hi.mono (by omega) (fun _ h => h))
    fun c ⟨hcl, hcp, hcf, hci, hcr, hcrc, hcmarkers, hcsh, hcc, hcfra⟩ => ?_).mono
      (by omega) (fun _ h => h)
  have hcq : c.env modulusVar = q := by rw [hcfra _ (by decide)]; exact hbq
  have hcin : C.inp.drop c.ip = binary L n ++ rest := by rw [hci]; exact hbin
  have hl := streamPayloadLoop_spec C store (binary L n) rest ((a.ram store).drop (L + 1))
    c hcc q 0 1 (by omega) hcq hcl hcp (by omega) (by omega) hfit
    (by simpa only [binary_length] using hcf) hcin
    (by simpa only [binary_length] using hcmarkers)
  rw [binary_length] at hl
  refine hl.mono le_rfl ?_
  rintro d ⟨hdl, _hdp, _hdz, hdi, hdr, hdrc, hdsh, hdc, hdf⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hdsh.trans (hcsh.trans hbsh), hdc, ?_⟩
  · simpa only [Nat.zero_add, Nat.one_mul,
      binary_value L n (lt_natBitLength n)] using hdl
  · rw [hdi, hci, hbi, NearCubicGates.Close.Cells.natWord_length]
    dsimp only [L]
    omega
  · rw [hdr, hcr, hbr]
  · simp only [hdrc, hcrc, Function.update_self]
    omega
  · intro other ho
    have hrcother : d.rc other = b.rc other := by
      rw [hdrc, hcrc, Function.update_of_ne ho, Function.update_of_ne ho]
    have hramother : d.ram other = b.ram other := by rw [hdr, hcr]
    obtain ⟨hr, hrc⟩ := hbo other ho
    exact ⟨hramother.trans hr, hrcother.trans hrc⟩
  · exact (hbf.weaken (by simp [payloadBodyScratch])).trans (hcfra.trans hdf)

end NearQuarticWires.StageLift
