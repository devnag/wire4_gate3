import Proof.Quartic.StageCertNative.EntryRequest
import Proof.Quartic.StageCertNative.CountRun
import Proof.Quartic.StagePrint.NativeCensus
import Proof.Quartic.StageNativeWidth.PackedFit
import Proof.Quartic.StageCertSourceBounds.Source

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Tabulator
open StageCertificateControl StageCert.Tokens

noncomputable def termRequest {B1 B2 : ℕ} (r : IndexedRequest B1 B2)
    (i : Fin (termCount r)) : StageTuple.TermCutRequest :=
  (exactEntry (actualMoment r i)).termRequest

noncomputable def commonWidth {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  (termRequest r ⟨0,termCount_pos r⟩).stackWidth

theorem termRequest_width {B1 B2 : ℕ} (r : IndexedRequest B1 B2)
    (i : Fin (termCount r)) : (termRequest r i).stackWidth=commonWidth r := by
  rfl

/-- `lem:print`, paper/paper.tex: the complete
whole-test equality stream concatenates the actual expanded Terms
in the original low-first population or closed-walk order. -/
noncomputable def wholeCuts {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    List MatrixScoreBatch.Cut :=
  (List.ofFn (fun i : Fin (termCount r)=>StagePrint.nativeEqualityCuts (termRequest r i))).flatten

/-- `lem:print`, paper/paper.tex: each original
term uses the unchanged sharp original-child census, with no
additional maximum-child or larger polynomial-variable bank. -/
theorem termCuts_count {B1 B2 : ℕ} (r : IndexedRequest B1 B2)
    (i : Fin (termCount r)) :
    (StagePrint.nativeEqualityCuts (termRequest r i)).length≤
      r.prepared.selected.1.Uocc^(16*r.prepared.selected.1.Xmax+8*r.prepared.selected.1.k) := by
  let m:=actualMoment r i
  have hs:=m.rules
  have hkids : ∀j,(m.nativeContext.nativeKids j).length≤ m.selected.1.childCap := by
    intro j
    rw [hs.childCap_eq]
    exact m.nativeContext.nativeKids_length_le j hs.n_pos
  have hc:=StagePrint.nativeEqualityCuts_count_le (termRequest r i) m.selected.1.childCap hkids
  have hg:=StageCertSourceBounds.actual_gate_count_le m
  have hbase : 1+17*(Builder.allGates m.call).length*m.selected.1.childCap≤ m.selected.1.Uocc := by
    rw [hs.Uocc_eq,hs.NatAtoms_eq,hs.m_eq]
    change 1+17*(Builder.allGates m.call).length*m.selected.1.childCap≤
      1+17*(2*m.call.n^4)*m.selected.1.childCap
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hg)) 1
  exact hc.trans (Nat.pow_le_pow_left hbase _)

/-- `lem:print` and `prop:time`, paper/paper.tex: summing every actual equality stream stays inside
the original strict degree reserve, for every proposed witness. -/
theorem wholeCuts_count {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (wholeCuts r).length≤2^((r.prepared.call.n-r.prepared.selected.1.k)/100) := by
  have hs:=Cells.prepare_spec _ r.prepared.selected.1 r.prepared.selected.2
  let D:=16*r.prepared.selected.1.Xmax+8*r.prepared.selected.1.k
  have hD : D≤r.prepared.selected.1.Dmax := by
    have hh:=hs.moment_degree
    rw [hs.m_eq] at hh
    exact hh
  have hc : (wholeCuts r).length≤termCount r*r.prepared.selected.1.Uocc^D := by
    unfold wholeCuts
    rw [List.length_flatten]
    have hh:=List.sum_le_card_nsmul
      ((List.ofFn fun i : Fin (termCount r)=>StagePrint.nativeEqualityCuts (termRequest r i)).map List.length)
      (r.prepared.selected.1.Uocc^D) (by
        intro value hv
        obtain ⟨cuts,hcuts,rfl⟩:=List.mem_map.mp hv
        obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hcuts
        exact termCuts_count r i)
    simpa only [List.length_map,List.length_ofFn,smul_eq_mul] using hh
  have hN : termCount r≤2^(4*r.prepared.selected.1.k) := by
    have hh:=termCount_le_eighth r
    rw [hs.N_eq,←pow_mul] at hh
    have he : r.prepared.selected.1.k/2*8≤4*r.prepared.selected.1.k := by omega
    exact hh.trans (Nat.pow_le_pow_right (by decide) he)
  have hp:=hs.printing_entries D hD
  rw [hs.m_eq] at hp
  exact (hc.trans (Nat.mul_le_mul_right _ hN)).trans hp

end NearQuarticWires.StageCertNative
