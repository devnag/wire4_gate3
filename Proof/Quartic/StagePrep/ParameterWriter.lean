import Proof.Quartic.StagePrep.ParameterLayout

/-!
# The complete physical parameter serializer

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter
open NearCubicWires.RepairRepresentation

/-- The literal scalar, prime and factor serializer for
`sec:params`, paper/paper.tex. The factor chain
is executed again with binary emission only after admission. -/
def parameterWriter : St VV :=
  .seq (printVars parameterHeadRegisters)
    (.seq prPrint (.seq (printVars parameterTailRegisters) (chainP true)))

/-- All word emission and repeated factor-chain work of
`sec:params`, paper/paper.tex. -/
def parameterWriterCost (P J h Wd : ℕ) : ℕ :=
  parameterHeadRegisters.length * (pvCost Wd + 1) + 1 +
    prPrintCost P Wd + parameterTailRegisters.length * (pvCost Wd + 1) + 1 +
    chainCost J h + 10

/-- The actual integer serializer of `sec:params`,
paper/paper.tex, emits the complete public
record, including both lists and all rational signs. The second
factor computation is included in the execution budget. -/
theorem parameterWriter_spec (C : Ctx) (a : DS VV) (hc : Cst a) (hv : Valid C a)
    (p : Cells.Parameters) (n N D h : ℕ) (x : ℚ)
    (hhead : parameterHeadRegisters.flatMap (fun v => natWord (a.env v)) = parameterHeadWord p)
    (htail : parameterTailRegisters.flatMap (fun v => natWord (a.env v)) = parameterTailWord p)
    (hPv : a.env pP = p.P) (hprimes : p.primes = dyadicPrimes p.P)
    (hN : a.env pXN = N) (hD : a.env pXD = D) (hJ : a.env pJM = Jmax n)
    (hx : x = (N : ℚ) / D) (hN0 : 0 < N) (hND : N ≤ D) (hDle : D ≤ (h + 32) * N)
    (hstop : stopIndex x n = some p.factors.length)
    (hfactors : chainFactors x p.factors.length = p.factors)
    (hW : 1024 * D + (h + 33) * (h + 33) + Jmax n + 1000 < 2 ^ C.Wd)
    (hPW : 2 * (p.P + 1) + 8 < 2 ^ C.Wd) (hW3 : 3 ≤ C.Wd) :
    Hs C parameterWriter a (parameterWriterCost p.P (Jmax n) h C.Wd)
      (fun b => b.out = a.out ++ Program.parametersWord p ∧
        b.cp = a.cp ∧ b.wq = a.wq ∧ Cst b ∧ Valid C b ∧
        FrS a b (pvT ++ prPT ++ chT)) := by
  unfold parameterWriter
  refine Hx.hs (Hs.then (printVars_spec parameterHeadRegisters
    parameter_registers_printable.1 hW3 a hc hv)
    (fun b ⟨hbout, hbcp, hbwq, hbc, hbvalid, hbfr⟩ n1 hn1 => ?_))
  have hbP : b.env pP = p.P := (hbfr _ (by decide) (by decide)).trans hPv
  refine Hs.then (prPrint_spec b hbc hbvalid p.P hbP hW3 hPW)
    (fun d ⟨hdout, hdcp, hdwq, hdc, hdvalid, hdfr⟩ n2 hn2 => ?_)
  have F : FrS a d (pvT ++ prPT) :=
    FrS.trans (FrS.weaken hbfr (by decide)) (FrS.weaken hdfr (by decide))
  have hsafe : ∀ v ∈ parameterTailRegisters, v ∉ pvT ++ prPT := by decide
  have hdtail : parameterTailRegisters.flatMap (fun v => natWord (d.env v)) =
      parameterTailWord p := by
    rw [← htail]
    apply List.flatMap_congr
    intro v hvv
    rw [F v (parameter_registers_printable.2 v hvv).1 (hsafe v hvv)]
  refine Hs.then (printVars_spec parameterTailRegisters
    parameter_registers_printable.2 hW3 d hdc hdvalid)
    (fun e ⟨heout, hecp, hewq, hec, hevalid, hefr⟩ n3 hn3 => ?_)
  have F' : FrS a e (pvT ++ prPT) :=
    FrS.trans F (FrS.weaken hefr (by decide))
  have heN : e.env pXN = N := (F' _ (by decide) (by decide)).trans hN
  have heD : e.env pXD = D := (F' _ (by decide) (by decide)).trans hD
  have heJ : e.env pJM = Jmax n := (F' _ (by decide) (by decide)).trans hJ
  refine Hs.last (Hs.addValid (by omega) hevalid
    (chainP_spec e hec true x n N D h heN heD heJ hx hN0 hND hDle hW (by omega))) ?_
  rintro f ⟨⟨⟨i, hfi, hfA, hfout, hfstop⟩, hfAD, hfiJ, hfcp, hfwq, hfc, hffr⟩, hfvalid⟩ n4 hn4
  have hi : i = p.factors.length := by
    rcases hfstop with ⟨_, hs⟩ | ⟨_, hs⟩
    · rw [hstop] at hs
      exact (Option.some.inj hs).symm
    · rw [hstop] at hs
      cases hs
  refine ⟨⟨?_, hfcp.trans (hecp.trans (hdcp.trans hbcp)),
    hfwq.trans (hewq.trans (hdwq.trans hbwq)), hfc, hfvalid,
    FrS.trans (FrS.weaken F' (by decide)) (FrS.weaken hffr (by decide))⟩, ?_⟩
  · rw [hfout, heout, hdout, hbout, hhead, hdtail, hi, hfactors]
    rw [parametersWord_layout, hprimes]
    simp only [↓reduceIte, List.append_assoc]
  · unfold parameterWriterCost
    omega

end NearQuarticWires.StagePrep
