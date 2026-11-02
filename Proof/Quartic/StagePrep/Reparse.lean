import Proof.Quartic.StagePrep.Admission
import Proof.Gates.Dispatch.Main

/-!
# The parsed admission pass after the wire census

Paper: normalized calls, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open Classical

/-- Returning to the public call header of `sec:counting`, paper/paper.tex leaves the witness cursor unchanged. -/
def rewindCall : St VV := .seq (.op .rstC) (.op (.zero vPOS))

/-- The call rewind of `sec:counting`, paper/paper.tex takes three
steps, modifies only its cursor register, and reads no witness bit. -/
theorem rewindCall_spec (C : Ctx) (a : DS VV) (hc : Cst a) :
    Hs C rewindCall a 3 (fun b => b.cp = 0 ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Cst b ∧ Fr a b [vPOS]) := by
  unfold rewindCall
  refine Hs.seq (t2 := 1) (hs_rstC C a) ?_
  rintro b rfl
  refine Hs.mono (hs_zero C vPOS _) le_rfl ?_
  rintro d rfl
  exact ⟨rfl, rfl, rfl,
    ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z,
     by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one,
     by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two,
     by simp⟩,
    fun x hx => DS.set_env_ne _ _ (by simpa using hx)⟩

/-- The exact structural, precision, actual-wire and unit-top
checks for `sec:counting`, paper/paper.tex. -/
def parseAdmission (B1 B2 : ℕ) : St VV :=
  .seq rewindCall (.seq parseCall (admitQuartic B1 B2))

/-- The complete admission pass for `sec:counting`, paper/paper.tex
preserves the physical census and returns the exact parsed call. -/
theorem parseAdmission_spec (C : Ctx) (B1 B2 : ℕ) (c : Call)
    (a : DS VV) (hc : Cst a)
    (ht : a.env censusTotal = Transfer.callWires c)
    (hu : a.env censusUnit = bnat (Transfer.UnitTop c.first ∧ Transfer.UnitTop c.second))
    (hcw : C.cw = callWord c) (hW : 2 * C.cw.length + 8 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (hA : (B1 + B2 + 5) * ((callWord c).length + 1) ≤ C.Wd) :
    Hs C (parseAdmission B1 B2) a (parseCost C.cw.length + admCost B1 B2 + 40)
      (fun b => ParseOut c b ∧ b.env vADM = bnat (Transfer.Admitted4 B1 B2 c) ∧
        b.env censusTotal = Transfer.callWires c ∧
        b.env censusUnit = bnat (Transfer.UnitTop c.first ∧ Transfer.UnitTop c.second) ∧
        b.cp = (callWord c).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
        Fr a b (vPOS :: parseT ++ admT')) := by
  classical
  unfold parseAdmission
  refine Hx.hs (Hs.then (rewindCall_spec C a hc)
    (fun b ⟨hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  refine Hs.then (parseCall_spec c b hbc hbcp hcw hW hL)
    (fun d ⟨hdp, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2 => ?_)
  have hdt : d.env censusTotal = Transfer.callWires c := by
    rw [hdfr _ (by decide), hbfr _ (by decide), ht]
  have hdu : d.env censusUnit = bnat (Transfer.UnitTop c.first ∧ Transfer.UnitTop c.second) := by
    rw [hdfr _ (by decide), hbfr _ (by decide), hu]
  refine Hs.last (admitQuartic_spec C B1 B2 c d hdc hdp hdt hdu hA)
    (fun e ⟨hef, hecp, hewq, heout, hec, hefr⟩ n3 hn3 => ?_)
  have hep : ParseOut c e := by
    apply hdp.congr
    intro y hy1 hy2
    apply hefr y
    intro h
    have hm : ∀ z ∈ admT', z.val < 17 ∨ 56 ≤ z.val := by decide
    have hz := hm y h
    omega
  refine ⟨⟨hep, hef, ?_, ?_, hecp.trans hdcp,
    hewq.trans (hdwq.trans hbwq), heout.trans (hdout.trans hbout), hec,
    Fr.trans (Fr.weaken hbfr (by decide))
      (Fr.trans (Fr.weaken hdfr (by decide)) (Fr.weaken hefr (by decide)))⟩, by omega⟩
  · exact (hefr _ (by decide)).trans hdt
  · exact (hefr _ (by decide)).trans hdu

end NearQuarticWires.StagePrep
