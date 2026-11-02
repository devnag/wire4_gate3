import Proof.Quartic.StagePrep.WitnessBit
import Proof.Quartic.Program.Prefix

/-!
# The bounded witness-prefix loop

Paper: `sec:algorithm`, paper/paper.tex, and
`prop:time`. The loop bound is public call data.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.WordPrograms
open NearCubicWires NearCubicWires.RepairOrdinary

/-- The counter for the witness prefix of `sec:algorithm`, paper/paper.tex. -/
def prefixIndex : Fin VV := ⟨240, by decide⟩

/-- The public prefix length of `sec:algorithm`, paper/paper.tex. -/
def prefixLimit : Fin VV := ⟨241, by decide⟩

/-- The zero-filled prefix of `sec:algorithm`, paper/paper.tex. -/
def prefixBits (w : List Bool) (k : ℕ) : List Bool :=
  (List.range k).map fun j => w.getD j false

/-- One additional prefix bit of `sec:algorithm`, paper/paper.tex. -/
theorem prefixBits_succ (w : List Bool) (k : ℕ) :
    prefixBits w (k + 1) = prefixBits w k ++ [w.getD k false] := by
  simp [prefixBits, List.range_succ]

/-- The saturated read cursor has the same zero-filled bit as the
logical prefix cursor, as specified in `sec:algorithm`, paper/paper.tex. -/
theorem witnessBit_min (w : List Bool) (k : ℕ) :
    w.getD (min k w.length) false = w.getD k false := by
  by_cases hk : k < w.length
  · rw [Nat.min_eq_left hk.le]
  · rw [Nat.min_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ k)]

/-- A marked bit and a counter increment for the witness in
`sec:algorithm`, paper/paper.tex. -/
def prefixBody : St VV := .seq framedWitnessBit (.op (.inc prefixIndex))

/-- The prefix loop of `sec:algorithm`, paper/paper.tex. -/
def prefixLoop : St VV := .loop (.lt prefixIndex prefixLimit) prefixBody

/-- The loop of `sec:algorithm`, paper/paper.tex emits exactly the
requested marked prefix and executes at most ten steps per bit. -/
theorem prefixLoop_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (l : ℕ) (hindex : a.env prefixIndex = 0) (hlimit : a.env prefixLimit = l)
    (hwq : a.wq = 0) (hl : l < 2 ^ C.Wd) :
    Hs C prefixLoop a (10 * l + 2) (fun b =>
      b.out = a.out ++ (prefixBits C.wit l).flatMap (fun bit => [true, bit]) ∧
      b.cp = a.cp ∧ b.wq = min l C.wit.length ∧
      b.env prefixIndex = l ∧ b.env prefixLimit = l ∧ Cst b ∧
      Fr a b [t0, prefixIndex]) := by
  let I : ℕ → DS VV → Prop := fun k b =>
    b.out = a.out ++ (prefixBits C.wit k).flatMap (fun bit => [true, bit]) ∧
    b.cp = a.cp ∧ b.wq = min k C.wit.length ∧
    b.env prefixIndex = k ∧ b.env prefixLimit = l ∧ Cst b ∧
    Fr a b [t0, prefixIndex]
  have hloop := Hs.loopN (C := C) (c := .lt prefixIndex prefixLimit)
    (s := prefixBody) (by change prefixIndex ≠ prefixLimit; decide) I l 8 ?_ ?_ a ?_
  · simpa [prefixLoop, I, Nat.mul_comm] using hloop
  · intro k hk b hb
    obtain ⟨hbout, hbcp, hbwq, hbi, hbl, hbc, hbfr⟩ := hb
    refine ⟨by simp [Cnd.eval, hbi, hbl, hk], ?_⟩
    unfold prefixBody
    refine Hs.seq (t2 := 1) (framedWitnessBit_spec C b hbc) ?_
    rintro d ⟨hdout, hdcp, hdwq, hdc, hdfr⟩
    have hdi : d.env prefixIndex = k := by rw [hdfr _ (by decide), hbi]
    refine Hs.mono (hs_inc C prefixIndex d (by rw [hdi]; omega)) le_rfl ?_
    rintro e rfl
    refine ⟨?_, hdcp.trans hbcp, ?_, ?_, ?_, ?_, ?_⟩
    · rw [DS.set_out, hdout, hbwq, witnessBit_min, hbout, prefixBits_succ]
      simp [List.flatMap_append, List.append_assoc]
    · rw [DS.set_wq, hdwq, hbwq]
      split_ifs with h
      · omega
      · omega
    · rw [DS.set_env_self, hdi]
    · rw [DS.set_env_ne _ _ (by decide), hdfr _ (by decide), hbl]
    · exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hdc.z,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hdc.one,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hdc.two,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hdc.pos⟩
    · exact Fr.trans hbfr (Fr.trans (Fr.weaken hdfr (by decide))
        (Fr.set _ _ (by decide)))
  · rintro b ⟨_, _, _, hbi, hbl, _⟩
    simp [Cnd.eval, hbi, hbl]
  · exact ⟨by simp [prefixBits], rfl, by simpa using hwq,
      hindex, hlimit, hc, Fr.refl a _⟩

/-- The list emitted by the prefix loop is the exact witness record
of `sec:algorithm`, paper/paper.tex. -/
theorem prefixBits_eq_witnessPrefix (c : NearCubicGates.Close.Interfaces.Call)
    (p : Cells.Parameters) (w : List Bool) :
    prefixBits w (Program.witnessReadLength c p) = Program.witnessPrefix c p w := by
  apply List.ext_getElem (by simp [prefixBits, Program.witnessPrefix])
  intro i hi hi'
  simp [prefixBits, Program.witnessPrefix, Algorithm.witnessBit]

end NearQuarticWires.StagePrep
