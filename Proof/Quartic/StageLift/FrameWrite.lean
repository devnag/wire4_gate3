import Proof.Quartic.StageLift.CallRetain

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearQuarticWires.StageMain.CallSkip

/-- `lem:print`, paper/paper.tex: one retained
source bit is read physically and written with its actual frame marker. -/
def emitMemoryFrameBit (store : Fin MM) : St VV MM :=
  .seq (.op (.rdM store t0)) (.seq (.op (.emit true)) (emitB .emit t0))

/-- `lem:print`, paper/paper.tex: the original
finite source is formatted as a literal framed word after a paid rewind,
without transferring any following Gamma-table bits to that source. -/
def emitMemoryFrame (store : Fin MM) : St VV MM :=
  .seq (.op (.rwM store))
    (.seq (forS c0 lengthCounter (emitMemoryFrameBit store)) (.op (.emit false)))

/-- `lem:print`, paper/paper.tex: one real
retained record produces its exact two-bit frame pair and advances only
that memory-source cursor, preserving every arithmetic register but t0. -/
theorem emitMemoryFrameBit_spec (C : Ctx) (store : Fin MM) (a : DS VV MM)
    (hc : Cst a) (bit : Bool) (hlt : a.rc store < (a.ram store).length)
    (hv : (a.ram store).getD (a.rc store) 0 = bit.toNat) :
    Hs C (emitMemoryFrameBit store) a 6 (fun b =>
      b.out = a.out ++ [true, bit] ∧ b.ip = a.ip ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc store (a.rc store + 1) ∧
      (b.kin, b.kout, b.kc) = (a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b [t0]) := by
  unfold emitMemoryFrameBit
  refine Hs.seq (t1 := 1) (t2 := 4) (hs_rdM C store t0 a hlt) fun b hb => ?_
  subst b
  let b := (a.set t0 ((a.ram store).getD (a.rc store) 0)).adv store
  have hbf : Fr a b [t0] := Fr.set a _ (by simp)
  have hbc := Cst.of_fr hc hbf (by decide)
  refine Hs.seq (t1 := 1) (t2 := 2) (hs_emit (C := C) true b) fun d hd => ?_
  subst d
  refine (emitB_spec (snkO C) t0 (by decide)
    ({ b with out := b.out ++ [true] }) ⟨hbc.z, hbc.one, hbc.two⟩ trivial).mono le_rfl ?_
  rintro d ⟨hdo, hdr, hde⟩
  have heq : decide (b.env t0 = 1) = bit := by
    simp only [b, DS.adv, DS.set_env_self, hv]
    cases bit <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change d.out = (b.out ++ [true]) ++ [decide (b.env t0 = 1)] at hdo
    rw [heq] at hdo
    simpa only [b, DS.adv, DS.set, List.append_assoc, List.singleton_append] using hdo
  · exact congrArg (fun t => t.1) hdr
  · exact congrArg (fun t => t.2.1) hdr
  · exact congrArg (fun t => t.2.2.1) hdr
  · exact congrArg (fun t => (t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hdr
  · exact ⟨(congrFun hde vZ).trans hbc.z, (congrFun hde v1).trans hbc.one,
      (congrFun hde v2).trans hbc.two⟩
  · intro x hx
    exact (congrFun hde x).trans (hbf x hx)

/-- `lem:print`, paper/paper.tex: the ordinary
frame consists of the literal marker/data pairs and one final marker. -/
theorem frame_eq_pairs (bits : List Bool) :
    frame bits = bits.flatMap (fun bit => [true, bit]) ++ [false] := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [frame, ih]

/-- `lem:print`, paper/paper.tex: the whole
retained finite source is emitted as its exact original frame, with
linear paid memory reads, rewind work and marker/data writes. -/
theorem emitMemoryFrame_spec (C : Ctx) (store : Fin MM) (bits : List Bool)
    (a : DS VV MM) (hc : Cst a) (ha : a.ram store = bits.map Bool.toNat)
    (hlen : a.env lengthCounter = bits.length) (hfit : bits.length < 2 ^ C.Wd) :
    Hs C (emitMemoryFrame store) a (a.rc store + 10 * bits.length + 8) (fun b =>
      b.out = a.out ++ frame bits ∧ b.ip = a.ip ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc store bits.length ∧
      (b.kin, b.kout, b.kc) = (a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b [c0, t0]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.out = a.out ++ (bits.take k).flatMap (fun bit => [true, bit]) ∧
    b.ip = a.ip ∧ b.ram = a.ram ∧ b.rc = Function.update a.rc store k ∧
    (b.kin, b.kout, b.kc) = (a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b [c0, t0]
  have hf := forS_spec' (C := C) c0 lengthCounter (by decide) (emitMemoryFrameBit store)
    (a.rew store) bits.length hfit I 6 ?_ ?_ hlen ?_
  · unfold emitMemoryFrame
    refine (Hs.seq (t1 := a.rc store + 1) (t2 := 10 * bits.length + 6)
      (hs_rwM C store a) fun b hb => ?_).mono (by omega) (fun _ h => h)
    subst b
    refine Hs.seq (t1 := 10 * bits.length + 4) (t2 := 1) (hf.mono (by omega) (fun _ h => h))
      fun b ⟨⟨hbo, hbi, hbr, hbrc, hbsh, hbc, hbf⟩, _, _⟩ => ?_
    refine (hs_emit (C := C) false b).mono le_rfl ?_
    rintro d rfl
    refine ⟨?_, hbi, hbr, hbrc, hbsh, ⟨hbc.z, hbc.one, hbc.two⟩, hbf⟩
    rw [hbo, frame_eq_pairs]
    simp only [List.take_length, List.append_assoc]
  · intro k b value ⟨hbo, hbi, hbr, hbrc, hbsh, hbc, hbf⟩
    exact ⟨hbo, hbi, hbr, hbrc, hbsh,
      Cst.of_fr hbc (Fr.set (T := [c0]) b value (by simp)) (by decide),
      hbf.trans (Fr.set _ _ (by simp))⟩
  · exact ⟨by simp [DS.rew], rfl, rfl, rfl, rfl, ⟨hc.z, hc.one, hc.two⟩, Fr.refl _ _⟩
  · intro k hk b ⟨hbo, hbi, hbr, hbrc, hbsh, hbc, hbf⟩ hbcounter hblen
    have hl : b.rc store < (b.ram store).length := by
      rw [hbr, ha, List.length_map, hbrc, Function.update_self]
      exact hk
    have hv : (b.ram store).getD (b.rc store) 0 = (bits[k]).toNat := by
      rw [hbr, ha, hbrc, Function.update_self,
        List.getD_eq_getElem _ _ (by simpa using hk)]
      simp only [List.getElem_map]
    refine (emitMemoryFrameBit_spec C store b hbc bits[k] hl hv).mono le_rfl ?_
    rintro d ⟨hdo, hdi, hdr, hdrc, hdsh, hdc, hdf⟩
    refine ⟨⟨?_, hdi.trans hbi, hdr.trans hbr, ?_, hdsh.trans hbsh, hdc,
      hbf.trans (hdf.weaken (by simp))⟩, ?_, ?_⟩
    · rw [hdo, hbo, List.take_succ_eq_append_getElem hk, List.flatMap_append]
      simp only [List.flatMap_singleton, List.append_assoc]
    · rw [hdrc, hbrc, Function.update_self, Function.update_idem]
    · rw [hdf c0 (by decide)]
      exact hbcounter
    · rw [hdf lengthCounter (by decide)]
      exact hblen

end NearQuarticWires.StageLift
