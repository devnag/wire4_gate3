import Proof.Quartic.StageLift.StreamNatural
import Proof.Quartic.StageLift.Constant
import Proof.Quartic.StageRecovery.PacketFields

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearQuarticWires.StageRecovery

/-- `lem:print`, paper/paper.tex: the complete
streaming signed decoder uses bounded sign and modular workspace only. -/
def signedStreamScratch : List (Fin VV) :=
  signVar :: productVar :: (payloadBodyScratch ++ rdNatT)

/-- `lem:print` and `lem:residue`, paper/paper.tex: read the actual bounded sign code, stream the arbitrary
magnitude directly modulo q, then normalize its sign modulo q. -/
def readSignedMod (store : Fin MM) : St VV MM :=
  .seq (readVariable signVar) (.seq (readNaturalMod store) reduceSignedCoefficient)

/-- `lem:print` and `lem:residue`, paper/paper.tex: every original signed integer index is decoded to its
literal nonnegative residue with no raw-magnitude or raw-bit-length
width hypothesis. Scratch marker rewinds are charged linearly. -/
theorem readSignedMod_spec (C : Ctx) (store : Fin MM) (z : ℤ) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a) (q : ℕ) (hq : 2 ≤ q)
    (haq : a.env modulusVar = q) (hfit : 2 * q ≤ 2 ^ C.Wd) (hW : 3 ≤ C.Wd)
    (hin : C.inp.drop a.ip = NearCubicGates.Close.Interfaces.intWord z ++ rest) :
    Hs C (readSignedMod store) a (a.rc store + 30 * natBitLength z.natAbs + 120) (fun b =>
      (b.env leftVar : ℤ) = z % (q : ℤ) ∧ b.env leftVar < q ∧
      b.ip = a.ip + (NearCubicGates.Close.Interfaces.intWord z).length ∧
      b.ram store = wr (a.ram store) 0 (List.replicate (natBitLength z.natAbs) 1 ++ [0]) ∧
      b.rc store = natBitLength z.natAbs + 1 ∧
      (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b signedStreamScratch) := by
  let negative := decide (z < 0)
  let sign := negative.toNat
  have hsignBits : natBitLength sign = 1 := by
    by_cases hz : z < 0 <;> simp [sign, negative, hz, natBitLength]
  have hword : NearCubicGates.Close.Interfaces.intWord z = natWord sign ++ natWord z.natAbs := by
    by_cases hz : z < 0 <;> simp [NearCubicGates.Close.Interfaces.intWord, sign, negative, hz]
  have her := readVariable_spec C a hc signVar (by decide) (by decide) sign
    (natWord z.natAbs ++ rest) (by simpa only [hword, List.append_assoc] using hin)
    (by rw [hsignBits]; exact hW)
  rw [hsignBits] at her
  unfold readSignedMod
  refine (Hs.seq (t1 := 62) (t2 := a.rc store + 30 * natBitLength z.natAbs + 53) her
    fun b ⟨hbs, hbi, hbrest, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.1) hbrest
  have hbrc : b.rc = a.rc := congrArg (fun t => t.2.2.1) hbrest
  have hbsmall : (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) :=
    congrArg (fun t => (t.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hbrest
  have hbq : b.env modulusVar = q := by rw [hbf _ (by decide)]; exact haq
  have hbin : C.inp.drop b.ip = natWord z.natAbs ++ rest := by
    rw [hbi, ← List.drop_drop, hin, hword, List.append_assoc, List.drop_left]
  have hn := readNaturalMod_spec C store z.natAbs rest b hbc q hq hbq hfit hbin
  rw [hbrc] at hn
  refine Hs.seq (t2 := 12) hn fun d ⟨hdl, hdi, hdr, hdrc, hdo, hdsh, hdc, hdf⟩ => ?_
  have hdq : d.env modulusVar = q := by rw [hdf _ (by decide)]; exact hbq
  have hds : d.env signVar = negative.toNat := by rw [hdf _ (by decide)]; exact hbs
  refine (reduceSignedCoefficient_spec C d hdc q (z.natAbs % q) negative (by omega)
    hdq hdl hds hfit).mono le_rfl ?_
  rintro e ⟨hel, hesh, hec, hef⟩
  have hs := Same.of_sh hesh
  have hcanonical : signedNaturalResidue q (z.natAbs % q) negative =
      signedNaturalResidue q z.natAbs negative := by
    simp [signedNaturalResidue]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hec, ?_⟩
  · rw [hel, hcanonical]
    exact signedNaturalResidue_eq q (by omega) z
  · rw [hel]
    unfold signedNaturalResidue
    split <;> exact Nat.mod_lt _ (by omega)
  · rw [hs.ip, hdi, hbi, hword, List.length_append]
    omega
  · rw [hs.ram, hdr, hbram]
  · rw [hs.rc, hdrc]
  · intro other ho
    simpa only [hs.ram, hs.rc, hbram, hbrc] using hdo other ho
  · rw [hs.out, hs.kin, hs.kout, hs.kc]
    exact hdsh.trans hbsmall
  · exact (hbf.weaken (by intro x hx; simp only [signedStreamScratch, List.mem_cons, List.mem_append] at hx ⊢; tauto)).trans
      ((hdf.weaken (by intro x hx; simp only [signedStreamScratch, List.mem_cons, List.mem_append]; tauto)).trans
        (hef.weaken (by intro x hx; simp only [signedStreamScratch, payloadBodyScratch,
          List.mem_cons, List.mem_append] at hx ⊢; tauto)))

end NearQuarticWires.StageLift
