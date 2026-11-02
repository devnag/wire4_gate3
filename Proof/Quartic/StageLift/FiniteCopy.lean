import Proof.Quartic.StageLift.FrameRead
import Proof.Quartic.StageMain.CallSkipMeasure
import Proof.Gates.Cells.Loop

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearQuarticWires.StageMain.CallSkip

/-- `lem:print`, paper/paper.tex: copy exactly
the measured finite source length, excluding every following table bit. -/
def copyFiniteInput (store : Fin MM) : St VV MM :=
  forS c0 lengthCounter (.seq (.op (.rdI t0)) (.op (.wrM store t0)))

/-- `lem:print`, paper/paper.tex: a physical
finite-word copy appends its actual bits to one record store, paying
for every input read and record write while preserving all other stores. -/
theorem copyFiniteInput_spec (C : Ctx) (store : Fin MM) (bits rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = bits ++ rest)
    (hlen : a.env lengthCounter = bits.length) (hfit : bits.length < 2 ^ C.Wd)
    (hcursor : a.rc store = (a.ram store).length) :
    Hs C (copyFiniteInput store) a (7 * bits.length + 4) (fun b =>
      b.ip = a.ip + bits.length ∧
      b.ram store = a.ram store ++ bits.map Bool.toNat ∧
      b.rc store = a.rc store + bits.length ∧
      (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [c0, t0]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.ip = a.ip + k ∧
    b.ram store = a.ram store ++ (bits.take k).map Bool.toNat ∧
    b.rc store = a.rc store + k ∧
    (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
    (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
    Cst b ∧ Fr a b [c0, t0]
  unfold copyFiniteInput
  refine (forS_spec' (C := C) c0 lengthCounter (by decide)
    (.seq (.op (.rdI t0)) (.op (.wrM store t0))) a bits.length hfit I 3 ?_
    ⟨by simp, by simp, by simp, fun _ _ => ⟨rfl, rfl⟩, rfl, hc, Fr.refl _ _⟩ hlen ?_).mono
      (by omega) ?_
  · intro k b value ⟨hbi, hbr, hbrc, hbo, hbsh, hbc, hbf⟩
    exact ⟨hbi, hbr, hbrc, hbo, hbsh,
      Cst.of_fr hbc (Fr.set (T := [c0]) b value (by simp)) (by decide),
      hbf.trans (Fr.set b value (by simp))⟩
  · intro k hk b ⟨hbi, hbr, hbrc, hbo, hbsh, hbc, hbf⟩ hbcounter hblen
    have hbin : C.inp.drop b.ip = bits[k] :: (bits.drop (k + 1) ++ rest) := by
      rw [hbi, ← List.drop_drop, hin, List.drop_append_of_le_length hk.le,
        List.drop_eq_getElem_cons hk]
      rfl
    refine Hs.seq (t1 := 1) (t2 := 1)
      (readInputBit_spec C t0 b bits[k] (bits.drop (k + 1) ++ rest) hbin) ?_
    rintro d rfl
    let d : DS VV MM := { b.set t0 (bits[k]).toNat with ip := b.ip + 1 }
    have hdcur : d.rc store = (d.ram store).length := by
      dsimp [d]
      rw [hbr, hbrc, List.length_append, List.length_map, List.length_take,
        Nat.min_eq_left hk.le, hcursor]
    refine (hs_wrM C store t0 d hdcur.le).mono le_rfl ?_
    rintro e rfl
    have hef : Fr b (d.put store (d.env t0)) [t0] := Fr.set b _ (by simp)
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, Cst.of_fr hbc hef (by decide), ?_⟩, ?_, ?_⟩
    · change b.ip + 1 = a.ip + (k + 1)
      omega
    · simp only [DS.put, Function.update_self]
      rw [putAt, if_neg (by omega)]
      change b.ram store ++ [(bits[k]).toNat] = _
      rw [hbr]
      simp only [List.take_succ_eq_append_getElem hk,
        List.map_append, List.map_singleton, List.append_assoc]
    · simp only [DS.put, Function.update_self]
      change b.rc store + 1 = _
      omega
    · intro other ho
      simpa only [DS.put, d, DS.set, Function.update_of_ne ho] using hbo other ho
    · exact hbsh
    · exact hbf.trans (hef.weaken (by simp))
    · rw [hef c0 (by decide)]
      exact hbcounter
    · rw [hef lengthCounter (by decide)]
      exact hblen
  · rintro b ⟨⟨hbi, hbr, hbrc, hbo, hbsh, hbc, hbf⟩, _, _⟩
    exact ⟨hbi, by simpa using hbr, hbrc, hbo, hbsh, hbc, hbf⟩

end NearQuarticWires.StageLift
