import Proof.Quartic.Cells.ParametersFinish
import Proof.Quartic.Cells.AsymptoticsHeight

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- `lem:asymptotics`, paper/paper.tex: every admitted
public input with polynomial precision eventually passes the actual finite
parameter computation, including its prime and rate-chain guards. -/
theorem eventual_prepare_isSome (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ x : ParameterInput, onset ≤ x.n → ValidInput x →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 → ∃ p, prepare x = some p := by
  obtain ⟨oc, hoc, hc⟩ := eventual_publicScales_core
  obtain ⟨od, hod, hd⟩ := eventual_publicScales_degree
  obtain ⟨op, hop, hp⟩ := eventual_publicScales_prime B1
  obtain ⟨om, hom, hm⟩ := eventual_publicScales_moment_degree B1
  obtain ⟨oh, hoh, hh⟩ := CoreRules.eventual_height B1
  refine ⟨max oc (max od (max op (max om oh))), by omega, ?_⟩
  intro x hn hv hb
  have hs := hc x (by omega) hv
  obtain ⟨hz, hdegree⟩ := hd x (by omega) hv
  obtain ⟨hprime, hbinary, _⟩ := hp x (by omega) hv hb
  have hmoment := (hm x (by omega) hv hb).trans hdegree.1
  have hheight := hh x (publicScales x) (availablePrime x (publicScales x))
    (by omega) hs hb hbinary
  obtain ⟨p, hfinish⟩ := finishSelection_isSome x (publicScales x) hs hz hprime hmoment hheight
  exact ⟨p, (prepare_eq_finish x hv hs.r_bound).trans hfinish⟩

/-- `sec:params` and `lem:asymptotics`, paper/paper.tex: the eventual successful computation supplies every canonical
finite parameter rule, with no later acceptance condition as an input. -/
theorem eventual_prepare (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ x : ParameterInput, onset ≤ x.n → ValidInput x →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      ∃ p, prepare x = some p ∧ ParameterRules x p := by
  obtain ⟨onset, hon, h⟩ := eventual_prepare_isSome B1
  refine ⟨onset, hon, ?_⟩
  intro x hn hv hb
  obtain ⟨p, hp⟩ := h x hn hv hb
  exact ⟨p, hp, prepare_spec x p hp⟩

end NearQuarticWires.Cells
