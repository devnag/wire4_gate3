import Proof.Quartic.StagePullback.Flags
import Proof.Gates.Cells.Arith

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

def metadataScratch : List (Fin VV) := [Offsets.blockWidth, Digits.radix, a1, c4, Flips.halfCount]

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: physically form the canonical block width,
radix and half count from the original scalar header. -/
def metadataProgram : St VV MM :=
  .seq (.op (.copy Offsets.blockWidth 22))
    (.seq (powP v2 23 Digits.radix)
      (.seq (.op (.copy Flips.halfCount 21)) (.op (.half Flips.halfCount))))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: all arithmetic metadata are actually computed with
linear cost in the syndrome width and preserve the original header. -/
theorem metadataProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams)
    (hc : Cst a) (hblock : a.env 22 = P.b) (hexp : a.env 23 = P.s)
    (hcount : a.env 21 = P.r) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C metadataProgram a (7 * P.s + 20) (fun b =>
      b.env Offsets.blockWidth = P.b ∧ b.env Digits.radix = 2 ^ P.s ∧
      b.env Flips.halfCount = P.r / 2 ∧ b.sh = a.sh ∧ Fr a b metadataScratch) := by
  have hb : P.b ≤ P.n :=
    (Nat.le_mul_of_pos_left _ P.r_pos).trans P.r_mul_b_le
  have hs : P.s ≤ P.n := P.s_le_b.trans hb
  have hn : P.n < 2 ^ C.Wd := (Flips.markerWidth C P hwidth).2.2.2
  unfold metadataProgram
  refine Hx.hs (Hs.then (hs_copy C Offsets.blockWidth 22 a (by decide))
    (fun b he n1 hn1 => ?_))
  subst he
  let b := a.set Offsets.blockWidth (a.env 22)
  have hbfr : Fr a b [Offsets.blockWidth] := Fr.set a _ (by simp)
  have hbc : Cst b := hc.of_fr hbfr (by decide)
  have hbe : b.env 23 = P.s := (hbfr _ (by decide)).trans hexp
  have hb2 : b.env v2 = 2 := hbc.two
  refine Hs.then (powP_spec v2 23 Digits.radix (by decide) b (by
    intro k hk
    rw [hbe] at hk
    rw [hb2]
    exact Nat.pow_lt_pow_right (by decide) (by omega))
    (by rw [hbe]; exact hs.trans_lt hn) (by
      have := Nat.one_le_two_pow (n := C.Wd - 1)
      have hh : 1 < 2 ^ C.Wd := Nat.one_lt_two_pow (by omega)
      exact hh)) (fun d ⟨hd, hds, hdf⟩ n2 hn2 => ?_)
  have hdc : Cst d := hbc.of_fr hdf (by decide)
  have hd21 : d.env 21 = P.r := (hdf _ (by decide)).trans ((hbfr _ (by decide)).trans hcount)
  have hdb : d.env Offsets.blockWidth = P.b :=
    (hdf _ (by decide)).trans (by simpa [b] using hblock)
  have hdr : d.env Digits.radix = 2 ^ P.s := by simpa only [hb2, hbe] using hd
  have hfa : Fr a b metadataScratch := hbfr.weaken (by
    intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    decide)
  have hfd : Fr b d metadataScratch := hdf.weaken (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> decide)
  refine Hs.then (hs_copy C Flips.halfCount 21 d (by decide)) (fun e he n3 hn3 => ?_)
  subst he
  refine Hs.last (hs_half C Flips.halfCount _) ?_
  rintro e he n4 hn4
  subst he
  refine ⟨⟨?_, ?_, ?_, hds, ?_⟩, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide : Offsets.blockWidth ≠ Flips.halfCount),
      DS.set_env_ne _ _ (by decide : Offsets.blockWidth ≠ Flips.halfCount)]
    exact hdb
  · rw [DS.set_env_ne _ _ (by decide : Digits.radix ≠ Flips.halfCount),
      DS.set_env_ne _ _ (by decide : Digits.radix ≠ Flips.halfCount)]
    exact hdr
  · simp only [DS.set_env_self, hd21]
  · exact hfa.trans (hfd.trans
      ((Fr.set d _ (by decide)).trans (Fr.set _ _ (by decide))))
  · rw [hbe] at hn2
    omega

end NearQuarticWires.StagePullback
