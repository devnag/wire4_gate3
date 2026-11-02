import Proof.Gates.TabMachine.Back
import Proof.Quartic.StagePrint.MatrixPackets

set_option autoImplicit false

namespace NearQuarticWires.StagePrint

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms.SInt (encS)

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the exact signed table of the separated cuts after the affine center pullback. -/
def cutTable (r : MatrixScoreBatch.Request) : Fin r.U → Fin r.U → ℤ :=
  SupplierPrinter.weightedDominance (MatrixScoreBatch.leftScore r)
    (MatrixScoreBatch.rightScore r) (MatrixScoreBatch.weight r)

/-- `lem:print`, paper/paper.tex: the physical table call followed by signed integer reconstruction. -/
noncomputable def signedTable (a : WilliamsAlgorithm)
    (qmap : Fin (CompetitorCountBanks.tapes (producer a) + 124) → Fin (ns + 1))
    (OUT : Fin (ns + 1)) (NR N2 QR Q1R K2 CO CP TOP SEEN : Fin nr) : WMX ns nr :=
  .seq (.mach (CompetitorCountTable.machine a) qmap)
    (decode (qmap (outSlot a)) OUT NR N2 QR Q1R K2 CO CP TOP SEEN)

/-- `lem:print`, paper/paper.tex: every integer reconstruction pass is included in the table budget. -/
noncomputable def signedTableCost (a : WilliamsAlgorithm) (r : MatrixScoreBatch.Request) (q : ℕ) : ℕ :=
  CompetitorCountTable.budget a r q + 1 + decodeCost (r.U * r.U) q

/-- `lem:print`, paper/paper.tex: the executed general affine-pullback table is reconstructed exactly, including negative coefficients. -/
theorem signedTable_spec (cap : ℕ) (a : WilliamsAlgorithm)
    {qmap : Fin (CompetitorCountBanks.tapes (producer a) + 124) → Fin (ns + 1)}
    {OUT : Fin (ns + 1)} {NR N2 QR Q1R K2 CO CP TOP SEEN : Fin nr}
    (hqmap : Function.Injective qmap) (hOUTq : ∀ j, qmap j ≠ OUT)
    (hR : [NR, N2, QR, Q1R, K2, CO, CP, TOP, SEEN].Nodup)
    (r : MatrixScoreBatch.Request) (q : ℕ) (σ : WState ns nr)
    (hinput : ∀ j, σ.st (qmap j) = CompetitorCountTable.input (producer a) r q false j)
    (hheads : ∀ j, σ.sh (qmap j) = 0)
    (hOUT : σ.st OUT = []) (hOUTh : σ.sh OUT = 0)
    (hN : σ.val NR = r.U * r.U) (hN2 : σ.val N2 = 0)
    (hQ : σ.val QR = q) (hQ1 : σ.val Q1R = q - 1) (hK2 : σ.val K2 = 0)
    (hCO : σ.val CO = 0) (hCP : σ.val CP = 0) (hT : σ.val TOP = 0) (hSE : σ.val SEEN = 0)
    (hq : 1 ≤ q) (hwidth : q ≤ CompetitorSameBucketColdDense.width r)
    (hbound : ∀ i j, (cutTable r i j).natAbs < 2 ^ (q - 1))
    (hcap : r.U * r.U * (2 * q + 3) + 2 * q + 4 ≤ cap) :
    Runs cap (signedTable a qmap OUT NR N2 QR Q1R K2 CO CP TOP SEEN) σ (signedTableCost a r q)
      (fun τ => τ.st OUT = recStream ((pvals false (cutTable r)).map fun z => binary (q + 1) (encS z)) ∧
        τ.sh OUT = 0 ∧ τ.val = σ.val ∧ τ.cell = σ.cell) := by
  let f : Fin r.U → Fin r.U → ℕ := fun i j => (cutTable r i j % 2 ^ q).toNat
  obtain ⟨actual, hr, _, hh, ht, _, _, _, _⟩ := CompetitorCountTable.cold_run a r q false f hwidth
    (by simp) (fun _ => toNat_emod_lt _ q) (fun _ => toNat_emod_modEq _ q)
  have hin : (fun j => σ.st (qmap j)) = CompetitorCountTable.input (producer a) r q false := funext hinput
  rw [← hin] at hr
  obtain ⟨τ, e, dock⟩ := WXExec.mach_run cap hqmap σ hheads hr
  have hout : τ.st (qmap (outSlot a)) = (CompetitorFinalTable.values false f).flatMap (binary q) ++ [] := by
    rw [List.append_nil, dock.st]
    change actual.final.tapes (CompetitorCountTable.slot (producer a) 141) = _
    exact ht
  have houthead : τ.sh (qmap (outSlot a)) = 0 := by
    rw [dock.sh, hh]
    unfold CompetitorCountTable.heads
    rw [outSlot_val]
    have hlarge := cb_large a
    split_ifs <;> omega
  obtain ⟨hother, hotherhead⟩ := dock.other OUT (fun j h => hOUTq j h)
  have hval : τ.val = σ.val := dock.val
  have hlen : (CompetitorFinalTable.values false f).length = r.U * r.U := by
    rw [CompetitorFinalTable.values_cardinality]
    simp
  have hv : ∀ v ∈ CompetitorFinalTable.values false f, v < 2 ^ q := by
    intro v hv
    change v ∈ WilliamsProductCertificate.rowMajorNatMatrix f at hv
    obtain ⟨i, j, rfl⟩ := mem_rowMajor f v hv
    exact toNat_emod_lt _ q
  have de := decode_spec cap (OP := qmap (outSlot a)) (OUT := OUT)
    (N := NR) (N2 := N2) (K := QR) (K1 := Q1R) (K2 := K2) (CO := CO) (CP := CP) (TOP := TOP) (SEEN := SEEN)
    (hOUTq _) hR τ q (CompetitorFinalTable.values false f) [] hq hv hout houthead
    (hother.trans hOUT) (hotherhead.trans hOUTh)
    (by rw [hval, hN, hlen]) (by rw [hval, hN2]) (by rw [hval, hQ]) (by rw [hval, hQ1])
    (by rw [hval, hK2]) (by rw [hval, hCO]) (by rw [hval, hCP]) (by rw [hval, hT]) (by rw [hval, hSE])
    (by rw [hlen]; exact hcap)
  have hm : (CompetitorFinalTable.values false f).map (tc q) = pvals false (cutTable r) :=
    values_map false f (cutTable r) (tc q) (fun i j => tc_residue q hq _ (hbound i j))
  have hm' : (CompetitorFinalTable.values false f).map (fun v => binary (q + 1) (encS (tc q v))) =
      (pvals false (cutTable r)).map (fun z => binary (q + 1) (encS z)) := by
    rw [← hm, List.map_map]
    rfl
  rw [hm'] at de
  refine ⟨_, (WXExec.seq e de).mono ?_, ?_, ?_, ?_, ?_⟩
  · unfold signedTableCost
    rw [hlen]
  · simp
  · simp [hotherhead, hOUTh]
  · simp [hval]
  · simp [dock.cell]

end NearQuarticWires.StagePrint
