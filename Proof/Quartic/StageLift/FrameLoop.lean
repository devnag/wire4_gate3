import Proof.Quartic.StageLift.FrameRead

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: retain an actual framed witness or Gamma-table word
once, ending immediately after its terminal marker. -/
def readFrame (store : Fin MM) : St VV MM :=
  .seq (.op (.rdI t0)) (.loop (.eq t0 v1) (frameReadBody store))

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the framed payload loop is linear in the number of
stored bits, with every marker and record write charged. -/
theorem frameLoop_spec (C : Ctx) (store : Fin MM) (bits rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hflag : a.env t0 = (frameFlag bits).toNat)
    (hin : C.inp.drop a.ip = framePayload bits ++ rest)
    (hcursor : a.rc store = (a.ram store).length) :
    Hs C (.loop (.eq t0 v1) (frameReadBody store)) a (8 * bits.length + 2) (fun b =>
      b.env t0 = 0 ∧ b.ip = a.ip + 2 * bits.length ∧
      b.ram store = a.ram store ++ bits.map Bool.toNat ∧
      b.rc store = a.rc store + bits.length ∧
      (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [t0, t1]) := by
  induction bits generalizing a with
  | nil =>
      have he : (Cnd.eq t0 v1).eval a = false := by
        simp [Cnd.eval, hflag, frameFlag, hc.one]
      refine ⟨a, 2, Ex.loopF (show t0 ≠ v1 by decide) he, by simp, ?_⟩
      exact ⟨by simpa [frameFlag] using hflag, by simp, by simp, by simp,
        fun _ _ => ⟨rfl, rfl⟩, rfl, hc, Fr.refl _ _⟩
  | cons bit bits ih =>
      have he : (Cnd.eq t0 v1).eval a = true := by
        simp [Cnd.eval, hflag, frameFlag, hc.one]
      have hinput : C.inp.drop a.ip = bit :: frameFlag bits :: (framePayload bits ++ rest) := by
        change C.inp.drop a.ip = (bit :: frame bits) ++ rest at hin
        rw [frame_decompose bits] at hin
        simpa only [List.cons_append] using hin
      obtain ⟨b, n, hb, hn, hbeq⟩ := frameReadBody_spec C store a bit (frameFlag bits)
        (framePayload bits ++ rest) hinput hcursor
      subst b
      have hbc : Cst (frameReadStep a store bit (frameFlag bits)) := by
        constructor
        · simpa (config := {decide := true}) [frameReadStep] using hc.z
        · simpa (config := {decide := true}) [frameReadStep] using hc.one
        · simpa (config := {decide := true}) [frameReadStep] using hc.two
      have hbf : Fr a (frameReadStep a store bit (frameFlag bits)) [t0, t1] := by
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        simp [frameReadStep, Function.update_of_ne hy.1, Function.update_of_ne hy.2]
      have hbin : C.inp.drop (frameReadStep a store bit (frameFlag bits)).ip =
          framePayload bits ++ rest := by
        change C.inp.drop (a.ip + 2) = _
        rw [← List.drop_drop, hinput]
        rfl
      have hbcur : (frameReadStep a store bit (frameFlag bits)).rc store =
          ((frameReadStep a store bit (frameFlag bits)).ram store).length := by
        simp only [frameReadStep, Function.update_self, List.length_append, List.length_singleton]
        rw [hcursor]
      obtain ⟨d, k, hd, hk, hdz, hdi, hdr, hdrc, hdother, hdsh, hdc, hdf⟩ :=
        ih (frameReadStep a store bit (frameFlag bits)) hbc
          (by simp [frameReadStep]) hbin hbcur
      refine ⟨d, n + k + 2, Ex.loopT (show t0 ≠ v1 by decide) he hb hd, by simp; omega, ?_⟩
      refine ⟨hdz, ?_, ?_, ?_, ?_, hdsh, hdc, hbf.trans hdf⟩
      · rw [hdi]
        change a.ip + 2 + 2 * bits.length = a.ip + 2 * (bit :: bits).length
        simp only [List.length_cons]
        omega
      · rw [hdr]
        simp [frameReadStep, List.map_cons, List.append_assoc]
      · rw [hdrc]
        simp only [frameReadStep, Function.update_self, List.length_cons]
        omega
      · intro other hother
        simpa only [frameReadStep, Function.update_of_ne hother] using hdother other hother

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the cold framed-word parser consumes the exact original
frame and preserves its following arbitrary source suffix. -/
theorem readFrame_spec (C : Ctx) (store : Fin MM) (bits rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = frame bits ++ rest)
    (hcursor : a.rc store = (a.ram store).length) :
    Hs C (readFrame store) a (8 * bits.length + 4) (fun b =>
      b.ip = a.ip + (frame bits).length ∧
      b.ram store = a.ram store ++ bits.map Bool.toNat ∧
      b.rc store = a.rc store + bits.length ∧
      (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [t0, t1]) := by
  unfold readFrame
  refine (Hs.seq (t2 := 8 * bits.length + 2)
    (readInputBit_spec C t0 a (frameFlag bits) (framePayload bits ++ rest)
      (by simpa only [frame_decompose, List.cons_append] using hin)) fun b hb => ?_).mono
      (by omega) (fun _ h => h)
  subst b
  have hbc : Cst ({ a.set t0 (frameFlag bits).toNat with ip := a.ip + 1 } : DS VV MM) := by
    constructor
    · simpa (config := {decide := true}) [DS.set] using hc.z
    · simpa (config := {decide := true}) [DS.set] using hc.one
    · simpa (config := {decide := true}) [DS.set] using hc.two
  have hinput : C.inp.drop (a.ip + 1) = framePayload bits ++ rest := by
    rw [← List.drop_drop, hin, frame_decompose]
    rfl
  refine (frameLoop_spec C store bits rest _ hbc (by simp) hinput hcursor).mono le_rfl ?_
  rintro b ⟨_hbz, hbi, hbr, hbrc, hbother, hbsh, hbc', hbf⟩
  refine ⟨?_, hbr, hbrc, hbother, hbsh, hbc', ?_⟩
  · simp only [frame_length] at *
    change b.ip = a.ip + 1 + 2 * bits.length at hbi
    omega
  · exact Fr.trans (Fr.set a _ (by simp)) hbf

end NearQuarticWires.StageLift
