import Proof.Quartic.StageGamma.QueryFrame
import Proof.Quartic.StageGamma.PairAccumulator

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: a complete
ORIGINAL term query computes its Gaussian count and signed coefficient,
then multiplies the exact prefix-restored count into both sign registers. -/
def gammaTermStep : St VV MM :=
  .seq gammaQuery (.seq prepareCoefficient prepareScaledTerm)

/-- `cor:conditional`, paper/paper.tex: a term's
entire physical scratch is disjoint from the ORIGINAL static state and
from the two accumulating sign sums. -/
def termScratch : List (Fin VV) :=
  queryScratch ++ coefficientPrepareScratch ++ scaledTermScratch

/-- `cor:conditional`, paper/paper.tex: signed
coefficient/count arithmetic preserves every ORIGINAL static register. -/
theorem staticRegisters_term : ∀ x : Fin VV, x ∈ staticRegisters →
    x ∉ coefficientPrepareScratch ∧ x ∉ scaledTermScratch := by
  decide

/-- `cor:conditional` and `prop:time`, paper/paper.tex: one complete actual ORIGINAL term is computed from its
address with all physical input writing, exact Gaussian work, signed
coefficient formation and prefix-restored multiplication charged. -/
theorem gammaTermStep_run (request : Machine.GammaRequest)
    (address : Fin ((request.parameters.Q + 1) ^ 8)) (width : ℕ) (input : List Bool)
    (a : DS VV MM) (ha : StaticReady request a)
    (haddress : a.env gammaAddress = address.val)
    (hwidth : 4 * Cycle.seedLength request.parameters + 10 ≤ width) :
    Hs (gaussContext width input (gaussInputReserve request) (gaussWorkReserve request))
      gammaTermStep a (2000010 * (Cycle.seedLength request.parameters + 9) ^ 6)
      (fun b =>
        b.env coefficientPositive =
          (originalTermPair request (littleChoiceEquiv request.parameters.Q address)).positive ∧
        b.env coefficientNegative =
          (originalTermPair request (littleChoiceEquiv request.parameters.Q address)).negative ∧
        StaticReady request b ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
        Fr a b termScratch) := by
  let C := gaussContext width input (gaussInputReserve request) (gaussWorkReserve request)
  let choice := littleChoiceEquiv request.parameters.Q address
  have hq := gammaQuery_frame request address width input a ha haddress (by omega)
  refine Hs.mono (Hs.seq
    (t1 := 2000001 * (Cycle.seedLength request.parameters + 9) ^ 6)
    (t2 := 129 + (5 * Cycle.seedLength request.parameters + 19) + 1) hq ?_) ?_ (fun _ h => h)
  · intro b ⟨be, bf, bstatic, bdigits, bo, br, brc, bfr⟩
    have bh := CachedHeader.fields request b bstatic.header
    refine Hs.seq (t1 := 129) (t2 := 5 * Cycle.seedLength request.parameters + 19)
      (prepareCoefficient_run C request choice b bstatic.header.2.2.2.2 bh.2.2.1 bstatic.side
        bdigits (by change Cycle.seedLength request.parameters + 1 ≤ width; omega)) ?_
    intro d ⟨dp, dn, ds, dc, df⟩
    have dstatic := StaticReady.preserve_registers request bstatic
      (fun x hx => df x (staticRegisters_term x hx).1) ds.ip
      (ds.kin.trans bstatic.header.2.2.2.1) dc
    have dh := CachedHeader.fields request d dstatic.header
    have de : d.env gammaExponent = kernelExponent request choice := by
      rw [df _ (by decide)]
      exact be
    have dflag : d.env gammaFlag = (kernelFlag request choice).toNat := by
      rw [df _ (by decide)]
      exact bf
    refine Hs.mono (prepareScaledTerm_run C request choice d dc dh.2.2.2.1 de dflag dp dn
      (by change 2 * Cycle.seedLength request.parameters + 1 ≤ width; omega))
      le_rfl ?_
    intro e ⟨ep, en, es, ec, ef⟩
    have estatic := StaticReady.preserve_registers request dstatic
      (fun x hx => ef x (staticRegisters_term x hx).2) es.ip
      (es.kin.trans dstatic.header.2.2.2.1) ec
    refine ⟨ep, en, estatic, es.out.trans (ds.out.trans bo),
      es.ram.trans (ds.ram.trans br), es.rc.trans (ds.rc.trans brc), ?_⟩
    have hqf : Fr a b termScratch := bfr.weaken (by
      intro x hx
      exact List.mem_append_left _ (List.mem_append_left _ hx))
    have hcf : Fr b d termScratch := df.weaken (by
      intro x hx
      exact List.mem_append_left _ (List.mem_append_right _ hx))
    have hsf : Fr d e termScratch := ef.weaken (fun x hx => List.mem_append_right _ hx)
    exact hqf.trans (hcf.trans hsf)
  · have hs : Cycle.seedLength request.parameters + 9 ≤
        (Cycle.seedLength request.parameters + 9) ^ 6 := by
      calc
        _ = (Cycle.seedLength request.parameters + 9) ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
    have hc : 150 ≤ (Cycle.seedLength request.parameters + 9) ^ 6 := by
      have hh : 9 ^ 6 ≤ (Cycle.seedLength request.parameters + 9) ^ 6 :=
        Nat.pow_le_pow_left (by omega) _
      omega
    nlinarith

end NearQuarticWires.StageGamma
