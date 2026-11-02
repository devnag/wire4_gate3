import Proof.Quartic.StagePrep.CanonicalProgram

/-!
# The successful preparation payload

Paper: `sec:params` and (W1)–(W3), paper/paper.tex, and preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter
open NearCubicGates.Close.Interfaces
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary

/-- The successful preparation output of `sec:params`,
paper/paper.tex, copies the original call,
serializes the whole parameter record and reads exactly the
publicly prescribed zero-filled witness prefix. -/
theorem successfulPreparationOutput_spec (C : Ctx) (a : DS VV)
    (hc : Cst a) (hv : Valid C a) (c : Call) (p : Cells.Parameters)
    (hcl : a.env vCL = C.cw.length) (hcw : C.cw = callWord c)
    (hhead : parameterHeadRegisters.flatMap (fun v => natWord (a.env v)) = parameterHeadWord p)
    (htail : parameterTailRegisters.flatMap (fun v => natWord (a.env v)) = parameterTailWord p)
    (hPv : a.env pP = p.P) (hprimes : p.primes = dyadicPrimes p.P)
    (N D h : ℕ) (x : ℚ)
    (hN : a.env pXN = N) (hD : a.env pXD = D) (hJ : a.env pJM = Jmax c.n)
    (hx : x = (N : ℚ) / D) (hN0 : 0 < N) (hND : N ≤ D) (hDle : D ≤ (h + 32) * N)
    (hstop : stopIndex x c.n = some p.factors.length)
    (hfactors : chainFactors x p.factors.length = p.factors)
    (hkv : a.env pK = p.k) (hJv : a.env pJ = p.J)
    (hG1 : a.env vG1 = Builder.occurrences c 0)
    (hG2 : a.env vG2 = Builder.occurrences c 1)
    (hwq : a.wq = 0)
    (hwidth : 1024 * D + (h + 33) * (h + 33) + Jmax c.n + 1000 < 2 ^ C.Wd)
    (hPW : 2 * (p.P + 1) + 8 < 2 ^ C.Wd) (hW3 : 3 ≤ C.Wd)
    (hCW : C.cw.length < 2 ^ C.Wd)
    (hprefix : Program.witnessReadLength c p + p.J +
      Builder.occurrences c 0 + Builder.occurrences c 1 + 16 < 2 ^ C.Wd) :
    Hs C successfulPreparationOutput a
      (C.cw.length * 8 + parameterWriterCost p.P (Jmax c.n) h C.Wd +
        10 * Program.witnessReadLength c p + 100)
      (fun b => b.out = a.out ++ (true :: (callWord c ++ Program.parametersWord p ++
        frame (Program.witnessPrefix c p C.wit))) ∧
        b.wq = min (Program.witnessReadLength c p) C.wit.length ∧
        b.cp = C.cw.length ∧ Cst b) := by
  let l := Program.witnessReadLength c p
  unfold successfulPreparationOutput preparationSequence
  refine Hx.hs (Hs.then (hs_emit C true a) (fun b hb n1 hn1 => ?_))
  subst hb
  have hcb : Cst { a with out := a.out ++ [true] } := ⟨hc.z, hc.one, hc.two, hc.pos⟩
  have hvb : Valid C { a with out := a.out ++ [true] } := ⟨hv.env_lt, hv.cp_le, hv.wq_le⟩
  refine Hs.then (copyCW_spec _ hcb hvb hcl hCW (by omega))
    (fun d ⟨hdout, hdcp, hdwq, hdc, hdvalid, hdfr⟩ n2 hn2 => ?_)
  have hsame : ∀ v : Fin VV, v.val < 200 → v ∉ [t0, vPOS, vJ] → d.env v = a.env v :=
    fun v hv' hnot => hdfr v hv' hnot
  have hdhead : parameterHeadRegisters.flatMap (fun v => natWord (d.env v)) = parameterHeadWord p := by
    rw [← hhead]
    apply List.flatMap_congr
    intro v hv'
    have hsafe : ∀ v ∈ parameterHeadRegisters, v.val < 200 ∧ v ∉ [t0, vPOS, vJ] := by decide
    rw [hsame v (hsafe v hv').1 (hsafe v hv').2]
  have hdtail : parameterTailRegisters.flatMap (fun v => natWord (d.env v)) = parameterTailWord p := by
    rw [← htail]
    apply List.flatMap_congr
    intro v hv'
    have hsafe : ∀ v ∈ parameterTailRegisters, v.val < 200 ∧ v ∉ [t0, vPOS, vJ] := by decide
    rw [hsame v (hsafe v hv').1 (hsafe v hv').2]
  refine Hs.then (parameterWriter_spec C d hdc hdvalid p c.n N D h x hdhead hdtail
    ((hsame _ (by decide) (by decide)).trans hPv) hprimes
    ((hsame _ (by decide) (by decide)).trans hN)
    ((hsame _ (by decide) (by decide)).trans hD)
    ((hsame _ (by decide) (by decide)).trans hJ)
    hx hN0 hND hDle hstop hfactors hwidth hPW hW3)
    (fun e ⟨heout, hecp, hewq, hec, _, hefr⟩ n3 hn3 => ?_)
  have heK : e.env pK = p.k :=
    (hefr _ (by decide) (by decide)).trans ((hsame _ (by decide) (by decide)).trans hkv)
  have heJ : e.env pJ = p.J :=
    (hefr _ (by decide) (by decide)).trans ((hsame _ (by decide) (by decide)).trans hJv)
  have heG1 : e.env vG1 = Builder.occurrences c 0 :=
    (hefr _ (by decide) (by decide)).trans ((hsame _ (by decide) (by decide)).trans hG1)
  have heG2 : e.env vG2 = Builder.occurrences c 1 :=
    (hefr _ (by decide) (by decide)).trans ((hsame _ (by decide) (by decide)).trans hG2)
  refine Hs.then (prefixLengthProgram_spec C e hec p.k p.J
    (Builder.occurrences c 0) (Builder.occurrences c 1) heK heJ heG1 heG2 hprefix)
    (fun f ⟨hfl, hfcp, hfwq, hfout, hfc, _⟩ n4 hn4 => ?_)
  have hfl' : f.env prefixLimit = l := hfl
  have hfwq' : f.wq = 0 := hfwq.trans (hewq.trans (hdwq.trans hwq))
  refine Hs.then (prefixReader_spec C f hfc l hfl' hfwq' (by omega))
    (fun g ⟨hgout, hgcp, hgwq, _, _, hgc, _⟩ n5 hn5 => ?_)
  refine Hs.last (skip_spec g) ?_
  rintro z rfl n6 hn6
  refine ⟨⟨?_, hgwq, hgcp.trans (hfcp.trans (hecp.trans hdcp)),
    hgc.set _ _ (by decide)⟩, by omega⟩
  rw [DS.set_out, hgout, hfout, heout, hdout, hcw,
    prefixBits_eq_witnessPrefix]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

end NearQuarticWires.StagePrep
