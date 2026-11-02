import Proof.Quartic.Reconstruct.PrintCount

/-!
# The run of the printing stage: input and context

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`printPreS` sets the constants, reads the input (`PrintHeadRun.printHeadS_spec`), computes `J`, the bit of two
circuits, `n_col` and the tables per group, and writes the framed context at depth `1` (`printPreS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord kindTag callWord)
open NearCubicWires.RepairOrdinary (frame)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {C : Ctx} {B1 B2 : ℕ}

/-- The input part and the context part of the printing stage. -/
def printPreS : St VV MM :=
  .seq NearCubicGates.Close.CounterMachine.PrefixProg.cstInit (.seq printHeadS (.seq calcA (.seq calcB (.seq calcC
    ctxWriteS))))

/-- The tables per group of a child. -/
noncomputable def tgOf (q : ChildRequest B1 B2) : ℕ :=
  ((q.selected.1.primes.sort (· ≤ ·)).map (groupSize (pairBit q))).sum

/-- The bounds used by `printPreS`. -/
structure PreBounds (q : ChildRequest B1 B2) (W : ℕ) : Prop where
  head : (callWord q.call).length + (parametersWord q.selected.1).length + 6 ≤ W
  pw : (prepWord B1 B2 q.call q.witness).length < 2 ^ W
  ncol : 2 ^ (q.call.n - q.selected.1.k) < 2 ^ W
  tg : tgOf q < 2 ^ W
  sq : ∀ p ∈ q.selected.1.primes.sort (· ≤ ·), p * p < 2 ^ W
  np : (q.selected.1.primes.sort (· ≤ ·)).length < 2 ^ W
  bits : ∀ v ∈ [q.call.n, q.selected.1.M1, q.selected.1.A, q.selected.1.Lambda, q.cellCall.J,
    (if kindTag q.call.kind = 1 then 1 else 0), 2 * Algorithm.traceOrder * Builder.occurrences q.call 0,
    2 * Algorithm.traceOrder * Builder.occurrences q.call 1, q.cellCall.ncol, tgOf q] ++ q.selected.1.factors,
    natBitLength v ≤ W - 3
  w6 : 6 ≤ W

/-- The state after `printPreS`. -/
structure MidDone (q : ChildRequest B1 B2) (b : DS VV MM) : Prop where
  jj : b.env kJ = q.cellCall.J
  hE : b.env kE = q.selected.1.hE
  pair : b.env kPair = pairBit q
  tg : b.env kG = tgOf q
  pl : b.env kPL = (prepWord B1 B2 q.call q.witness).length
  npc : b.env kPc = (q.selected.1.primes.sort (· ≤ ·)).length
  sp : b.ram sP = (prepWord B1 B2 q.call q.witness).map Bool.toNat
  sg : b.ram sG = (gammaTableWord q).map Bool.toNat
  spr : b.ram sPr = q.selected.1.primes.sort (· ≤ ·)
  rcok : ∀ m, b.rc m ≤ (b.ram m).length
  cst : Cst b
  ip : b.ip = (gammaWord q).length

/-- The cost of `printPreS` at width `W`. -/
noncomputable def printPreCost (q : ChildRequest B1 B2) (W : ℕ) : ℕ :=
  printHeadCost q + (q.call.n - q.selected.1.k) * 5 + 13 * (q.selected.1.primes.sort (· ≤ ·)).length +
    ctxCost (W - 3) q.cellCall.J q.cellCall.ncol + 33

theorem certifiedBits_length (q : ChildRequest B1 B2) : (certifiedBits q.cellCall).length = q.cellCall.ncol := by
  unfold certifiedBits; simp

/-- **The input and the context of the printing stage.** -/
theorem printPreS_spec (q : ChildRequest B1 B2) (hinp : C.inp = gammaWord q) (hB : PreBounds q C.Wd) :
    Hs C printPreS (a0 : DS VV MM) (printPreCost q C.Wd)
      (fun b => MidDone q b ∧ b.out = marksD 2 (contextWord q) ++ bitD 1 false) := by
  have hw := hB.w6
  refine Hx.hs (Hs.then (NearCubicGates.Close.CounterMachine.PrefixProg.cstInit_spec C (by omega))
    (fun d ⟨cd, dram, drc, dip, dout, _, _, _⟩ n0 hn0 => ?_))
  refine Hs.then (printHeadS_spec q d cd hinp dip (fun m => by rw [dram, drc]; exact ⟨rfl, rfl⟩) hB.head hB.pw)
    (fun b1 ⟨h1, o1⟩ n1 hn1 => ?_)
  refine Hs.then (calcA_spec b1 h1.cst _ _ h1.jj (rules q).J_pos h1.kind)
    (fun b2 ⟨j2, p2, s2, f2, c2⟩ n2 hn2 => ?_)
  have e2 : ∀ y, y ∉ [kJ, kPair] → b2.env y = b1.env y := f2
  refine Hs.then (calcB_spec b2 c2 q.call.n q.selected.1.k (by rw [e2 kN (by decide), h1.n])
    (by rw [e2 kK (by decide), h1.k]) hB.ncol) (fun b3 ⟨k3, s3, f3, c3⟩ n3 hn3 => ?_)
  have e3 : ∀ y, y ∉ [kT2, kC] → b3.env y = b2.env y := f3
  have ram3 : b3.ram = b1.ram := by rw [s3.ram, s2.ram]
  have rc3 : b3.rc = b1.rc := by rw [s3.rc, s2.rc]
  have rcok1 : ∀ m, b1.rc m ≤ (b1.ram m).length := fun m => by
    by_cases hm : m ∈ headStores
    · exact (h1.rcs m hm).le
    · rw [(h1.rest m hm).1, (h1.rest m hm).2]; exact le_rfl
  have pb3 : b3.env kPair = pairBit q := by rw [e3 kPair (by decide), p2, kindTag_bit]
  refine Hs.then (calcC_spec b3 c3 (by rw [ram3, rc3]; exact rcok1) (q.selected.1.primes.sort (· ≤ ·)) (pairBit q)
    (by rw [ram3, h1.pr]) (by rw [e3 kPc (by decide), e2 kPc (by decide), h1.npr]) pb3 hB.tg hB.sq hB.np)
    (fun b4 ⟨g4, o4, ip4, ram4, _, _, _, f4, rcok4, c4⟩ n4 hn4 => ?_)
  have e4 : ∀ y, y ∉ [kG, kI, t0, t3, t4] → b4.env y = b3.env y := f4
  have v4 : ∀ y, y ∉ [kG, kI, t0, t3, t4, kT2, kC, kJ, kPair] → b4.env y = b1.env y := fun y hy => by
    rw [e4 y (fun h => hy (by revert h; revert y; decide)), e3 y (fun h => hy (by revert h; revert y; decide)),
      e2 y (fun h => hy (by revert h; revert y; decide))]
  have hJ4 : b4.env kJ = q.cellCall.J := by rw [e4 kJ (by decide), e3 kJ (by decide), j2]; rfl
  have hP4 : b4.env kPair = (if kindTag q.call.kind = 1 then 1 else 0) := by
    rw [e4 kPair (by decide), e3 kPair (by decide), p2]
  have hC4 : b4.env kC = q.cellCall.ncol := by rw [e4 kC (by decide), k3, ncol_eq]
  refine Hs.last (ctxWriteS_spec b4 c4 rcok4 q.call.n q.selected.1.M1 q.selected.1.A q.selected.1.Lambda
    q.cellCall.J _ (2 * Algorithm.traceOrder * Builder.occurrences q.call 0)
    (2 * Algorithm.traceOrder * Builder.occurrences q.call 1) q.cellCall.ncol (tgOf q) q.selected.1.factors
    (certifiedBits q.cellCall) (by rw [v4 kN (by decide), h1.n]) (by rw [v4 kM (by decide), h1.m1])
    (by rw [v4 kA (by decide), h1.aa]) (by rw [v4 kL (by decide), h1.lam]) hJ4 hP4
    (by rw [v4 kB0 (by decide), h1.b0]) (by rw [v4 kB1 (by decide), h1.b1]) hC4 g4 (by rw [ram4, ram3, h1.fs])
    (factors_length q) (by rw [ram4, ram3, h1.zb]) (certifiedBits_length q) (C.Wd - 3) hB.bits (by omega))
    (fun b5 ⟨m5, c5⟩ n5 hn5 => ⟨⟨?_, ?_⟩, ?_⟩)
  · have k5 : ∀ y, y ∉ ctxT → b5.env y = b4.env y := m5.fr
    exact ⟨by rw [k5 kJ (by decide), hJ4], by rw [k5 kE (by decide), v4 kE (by decide), h1.hE],
      by rw [k5 kPair (by decide), e4 kPair (by decide), pb3], by rw [k5 kG (by decide), g4]; rfl,
      by rw [k5 kPL (by decide), v4 kPL (by decide), h1.pl], by rw [k5 kPc (by decide), v4 kPc (by decide), h1.npr],
      by rw [m5.ram, ram4, ram3, h1.pw], by rw [m5.ram, ram4, ram3, h1.gt], by rw [m5.ram, ram4, ram3, h1.pr],
      m5.rcok, c5, by rw [m5.ip, ip4, s3.ip, s2.ip, h1.ip]⟩
  · rw [m5.out, o4, s3.out, s2.out, o1, dout, contextWord_eq, List.nil_append]
    rfl
  · have hr : b3.rc sPr = (q.selected.1.primes.sort (· ≤ ·)).length := by
      rw [rc3, h1.rcs sPr (by decide), h1.pr]
    rw [hr] at hn4
    unfold printPreCost
    omega

end NearQuarticWires.Reconstruct
