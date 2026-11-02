import Proof.Quartic.StagePrep.ParameterRegisters

/-!
# The cached degree-comparison logarithm

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The cached printing-degree logarithm of `sec:params`,
paper/paper.tex. -/
def degreeLogReg : Fin VV := ⟨95, by decide⟩

/-- The logarithm computation used by the degree search of
`sec:params`, paper/paper.tex. -/
def degreeLogProgram : St VV :=
  .seq (.op (.copy t3 occurrenceCapReg)) (.seq clog2 (.op (.copy degreeLogReg t5)))

/-- The cached degree logarithm in `sec:params`,
paper/paper.tex, is the exact natural binary clog. -/
theorem degreeLogProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (U : ℕ) (hU : a.env occurrenceCapReg = U) (hW : 2 * U + 2 < 2 ^ C.Wd) :
    Hs C degreeLogProgram a (5 * Nat.clog 2 U + 10) (fun b =>
      b.env degreeLogReg = Nat.clog 2 U ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [t3, t5, t6, degreeLogReg]) := by
  unfold degreeLogProgram
  refine Hx.hs (Hs.then (hs_copy C t3 occurrenceCapReg a (by decide))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have hc0 : Cst (a.set t3 (a.env occurrenceCapReg)) := hc.set _ _ (by decide)
  have ht3 : (a.set t3 (a.env occurrenceCapReg)).env t3 = U := by rw [DS.set_env_self, hU]
  refine Hs.then (clog2_spec _ hc0 (by rw [ht3]; exact hW))
    (fun b ⟨hbl, _, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_)
  refine Hs.last (hs_copy C degreeLogReg t5 b (by decide)) ?_
  rintro d rfl n2 hn2
  refine ⟨⟨?_, hbcp, hbwq, hbout, hbc.set _ _ (by decide), ?_⟩, ?_⟩
  · rw [DS.set_env_self, hbl, ht3]
  · exact FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
      (FrS.trans (FrS.weaken hbfr.toS (by decide)) (Fr.toS (Fr.set _ _ (by decide))))
  · have hn1' : n1 ≤ 5 * Nat.clog 2 U + 6 := by simpa only [ht3] using hn1
    omega

end NearQuarticWires.StagePrep
