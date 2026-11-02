import Proof.Quartic.StageMainMask.EntryAcquire

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain.Compact StageMain.CallSkip StageLift

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the finite prepared header is physically measured and the original
input head is restored before source retention and witness decoding. -/
def measureEntryHeader : St VV MM := .seq scanPreparedPrefix
  (.seq (.op (.copy 41 lengthCounter))
    (.seq (.op (.copy compactLength lengthCounter)) rewindCompact))

/-- `prop:time`, paper/paper.tex: an actual header
scan, its runtime-length copies and every backward input move are charged. -/
theorem measureEntryHeader_run (C : Ctx) (c : Call) (p : Cells.Parameters)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = preparedPrefixWord c p ++ rest)
    (hwidth : (preparedPrefixWord c p).length + 2 ≤ C.Wd) :
    Hs C measureEntryHeader a
      (3000 * ((callWord c).length + 1) ^ 3 +
        4000 * ((Program.parametersWord p).length + 1) ^ 2 +
        5 * (preparedPrefixWord c p).length + 30) (fun b =>
      b.env 41 = (preparedPrefixWord c p).length ∧ b.ip = a.ip ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b) := by
  have hcap : (preparedPrefixWord c p).length < 2 ^ C.Wd :=
    lt_trans (by omega) Nat.lt_two_pow_self
  unfold measureEntryHeader
  apply Hx.hs
  refine Hs.then (scanPreparedPrefix_spec C c p rest a hc hin hwidth)
    (fun b ⟨hbip, hblen, hbrest, hbc, _hbfr⟩ n1 hn1 => ?_)
  refine Hs.then (hs_copy C 41 lengthCounter b (by decide)) (fun d hd n2 hn2 => ?_)
  subst hd
  let d := b.set 41 (b.env lengthCounter)
  have hdf : Fr b d [41] := Fr.set b _ (by simp)
  have hdc : Cst d := hbc.of_fr hdf (by decide)
  refine Hs.then (hs_copy C compactLength lengthCounter d (by decide))
    (fun e he n3 hn3 => ?_)
  subst he
  let e := d.set compactLength (d.env lengthCounter)
  have hef : Fr d e [compactLength] := Fr.set d _ (by simp)
  have hec : Cst e := hdc.of_fr hef (by decide)
  have helen : e.env compactLength = (preparedPrefixWord c p).length := by
    change d.env lengthCounter = _
    exact (hdf _ (by decide)).trans hblen
  refine Hs.last (rewindCompact_run C a.ip (preparedPrefixWord c p).length e hec hbip helen hcap) ?_
  rintro f ⟨hfip, hfrest, hfc, hffr⟩ n4 hn4
  refine ⟨⟨?_, hfip, hfrest.trans hbrest, hfc⟩, by omega⟩
  have he41 : e.env 41 = (preparedPrefixWord c p).length :=
    (hef 41 (by decide)).trans ((DS.set_env_self b 41 (b.env lengthCounter)).trans hblen)
  exact (hffr 41 (by decide)).trans he41

end NearQuarticWires.StageMainMask
