import Proof.Quartic.StageMainMask.StructuralRaw
import Proof.Quartic.StageMain.CircuitProgram

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageCert.Incidence

/-- `def:mask`, paper/paper.tex: the finite raw
source is traversed, its scalar suffix is actually decoded, and its
original gate occurrences determine the structural flag. -/
def structuralRawProgram : St VV :=
  .seq StageOutput.constants
    (.seq skipOriginalCall
      (.seq loadStructuralFields
        (.seq StageCert.structuralProgram
          (.seq (.op (.copy StageMain.tableResult patternFlag)) StageMain.emitCircuit))))

/-- `def:mask` and `prop:time`, paper/paper.tex: one initialized scalar program computes the exact
original-source structural bit from its literal finite input, with
its call traversal, field parsing, mask scans and output all paid. -/
theorem structuralRawProgram_spec {C : Ctx} (r : StructuralRawRequest)
    (hin : C.cw = r.word) (hW : 2 * C.cw.length + 8 ≤ C.Wd) :
    Hs C structuralRawProgram a0 (structuralRawSteps r C.cw.length)
      (fun b => b.out = [r.bit]) := by
  have henc := r.encoding_bounds
  have hgeom := r.geometry_bounds
  have hn : r.call.n ≤ C.cw.length := by rw [hin]; exact henc.1
  have hbN : r.partition.b ≤ C.cw.length := hgeom.2.1.trans hn
  have hrN : r.partition.r ≤ C.cw.length := hgeom.2.2.trans hn
  have hpow := Nat.lt_two_pow_self (n := C.Wd)
  have hL : C.cw.length + 2 < 2 ^ C.Wd := by omega
  have hbits : ∀ f ∈ structuralFields r.partition r.threshold r.left r.right,
      natBitLength f.2 + 2 ≤ C.Wd := by
    intro f hf
    have h := henc.2 f hf
    rw [← hin] at h
    omega
  unfold structuralRawProgram
  refine Hx.hs (Hs.then (StageOutput.constants_spec (C := C) (by omega))
    (fun a ⟨hac, hacp, _hawq, haout⟩ n1 hn1 => ?_))
  have hacw : C.cw.drop a.cp = callWord r.call ++
      (structuralFields r.partition r.threshold r.left r.right).flatMap (fun f => natWord f.2) := by
    rw [hacp, List.drop_zero, hin]
    rfl
  refine Hs.then (skipOriginalCall_spec r.call _ a hac hacw (by omega) hn)
    (fun b ⟨hbcp, _hbwq, hbout, hbc⟩ n2 hn2 => ?_)
  have hbcp' : b.cp = (callWord r.call).length := by rw [hbcp, hacp, Nat.zero_add]
  have hbin : C.cw.drop b.cp =
      (structuralFields r.partition r.threshold r.left r.right).flatMap (fun f => natWord f.2) ++ [] := by
    rw [hbcp', hin]
    simp only [StructuralRawRequest.word, List.drop_left, List.append_nil]
  refine Hs.then (loadStructuralFields_spec b hbc r.partition r.threshold r.left r.right []
    hbin hbits hL (by omega))
    (fun c ⟨hcfields, _hccp, _hcwq, hcout, hcc⟩ n3 hn3 => ?_)
  refine Hs.then (StageCert.structuralProgram_run C r.call _ r.partition r.threshold
    r.left r.right c hcc r.partition.b_pos hcfields.threshold hcfields.blockSize
    hcfields.radix hcfields.count hcfields.left hcfields.right hgeom.1
    hin hW (by omega) (by omega) (by omega) (by omega))
    (fun d ⟨hdflag, _hdwq, hdout, hdc, _hdfr⟩ n4 hn4 => ?_)
  refine Hs.then (hs_copy C StageMain.tableResult patternFlag d (by decide))
    (fun e he n5 hn5 => ?_)
  subst he
  let e := d.set StageMain.tableResult (d.env patternFlag)
  have hec : Cst e := hdc.set _ _ (by decide)
  have heflag : e.env StageMain.tableResult = r.bit.toNat := by
    rw [DS.set_env_self]
    exact hdflag
  refine Hs.last (StageMain.emitCircuit_spec e hec r.bit heflag) ?_
  rintro f hfout n6 hn6
  refine ⟨?_, ?_⟩
  · rw [hfout]
    change d.out ++ [r.bit] = _
    rw [hdout, hcout, hbout, haout, List.nil_append]
  · unfold structuralRawSteps
    omega

end NearQuarticWires.StageMainMask
