import Proof.Quartic.StagePrep.CensusCircuit
import Proof.Quartic.StagePrep.WireCap
import Proof.Quartic.Program.Output

/-!
# Admission for the wire-counted symmetric-top class

Paper: normalized calls, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open Classical

/-- The admission test of `sec:counting`, paper/paper.tex is the
existing normalized-call test, both unit tops, and the actual
physical wire cap. -/
theorem admitted4_iff_existing_checks (B1 B2 : ℕ) (c : Call) :
    Transfer.Admitted4 B1 B2 c ↔ c.Admitted B1 B2 ∧
      Transfer.UnitTop c.first ∧ Transfer.UnitTop c.second ∧
      Transfer.callWires c ≤ 2 * c.n ^ 4 := by
  constructor
  · intro h
    exact ⟨Program.admitted_of_admitted4 h, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.1⟩
  · rintro ⟨⟨hn, hw1, hw2, hk1, hk2, hp, _, hb1, hb2, hb3, hplen⟩, hu1, hu2, hw⟩
    exact ⟨hn, hw1, hw2, hu1, hu2, hk1, hk2, hp, hw, hb1, hb2, hb3, hplen⟩

/-- The admission program of `sec:counting`, paper/paper.tex adds
the actual wire cap and both unit-top tests to the parsed checks. -/
def admitQuartic (B1 B2 : ℕ) : St VV :=
  .seq (admitP B1 B2) (.seq testWireCap (needEq censusUnit v1))

/-- The physical test of `sec:counting`, paper/paper.tex computes
exactly `Admitted4` from the original parsed call and wire census. -/
theorem admitQuartic_spec (C : Ctx) (B1 B2 : ℕ) (c : Call)
    (a : DS VV) (hc : Cst a) (hp : ParseOut c a)
    (ht : a.env censusTotal = Transfer.callWires c)
    (hu : a.env censusUnit = bnat (Transfer.UnitTop c.first ∧ Transfer.UnitTop c.second))
    (hW : (B1 + B2 + 5) * ((callWord c).length + 1) ≤ C.Wd) :
    Hs C (admitQuartic B1 B2) a (admCost B1 B2 + 30) (fun b =>
      b.env vADM = bnat (Transfer.Admitted4 B1 B2 c) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b admT') := by
  classical
  obtain ⟨hpow, htw, _⟩ := admTwo_bounds B1 B2 c C.Wd hW
  unfold admitQuartic
  refine Hx.hs (Hs.then (admitP_spec B1 B2 c a hc hp hW)
    (fun b ⟨hbf, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  have hba : b.env vADM = bnat (c.Admitted B1 B2) := by
    rw [hbf]
    exact bnat_congr (admFlag_iff B1 B2 c)
  have hbn : b.env vN = c.n := (hbfr _ (by decide)).trans hp.n
  refine Hs.then (testWireCap_spec C b hbc _ hba
    (by simpa only [hbn] using hpow) (by simpa only [hbn] using htw))
    (fun d ⟨hdf, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2 => ?_)
  have hdu : d.env censusUnit = bnat (Transfer.UnitTop c.first ∧ Transfer.UnitTop c.second) := by
    rw [hdfr _ (by decide), hbfr _ (by decide), hu]
  refine Hs.last (needEq_spec censusUnit v1 (by decide) d _ hdf)
    (fun e ⟨hef, hecp, hewq, heout, hefr⟩ n3 hn3 => ?_)
  have hfr : Fr a e admT' := Fr.trans hbfr
    (Fr.trans hdfr (Fr.weaken hefr (by decide)))
  have hcp : e.cp = a.cp := hecp.trans (hdcp.trans hbcp)
  refine ⟨⟨?_, hcp, hewq.trans (hdwq.trans hbwq),
    heout.trans (hdout.trans hbout),
    Cst.of_fr hc hfr (by decide)
      (by rw [hfr _ (by decide), hcp]; exact hc.pos), hfr⟩, by omega⟩
  rw [hef]
  apply bnat_congr
  rw [hdu, hdc.one, bnat_eq_one, hbfr _ (by decide), ht, hbn,
    admitted4_iff_existing_checks]
  tauto

end NearQuarticWires.StagePrep
