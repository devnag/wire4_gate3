import Proof.Quartic.Reconstruct.PrintScanBase
import Proof.Quartic.Reconstruct.ReadListLen

/-!
# Reading a list into a store, counting

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`listInto m` reads `listWord natWord vs` into the empty store `m` and counts its bits in `lengthCounter`
(`listInto_spec`): it counts the list with the counting scanner `CallSkip.skipNatList`, moves back over it
(`rewindS`) and reads it into the store (`readListS`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord)
open NearQuarticWires.StageMain.CallSkip

variable {C : Ctx}

/-- The count before a list. -/
def kS : Fin VV := ⟨94, by decide⟩
/-- The number of bits of a list. -/
def kD : Fin VV := ⟨95, by decide⟩

/-- The number of primes. -/
def kPc : Fin VV := ⟨99, by decide⟩
/-- The number of rate factors. -/
def kFc : Fin VV := ⟨100, by decide⟩

/-- Read a list of numbers into store `m`, counting; keep its length in `x`. -/
def listInto (m : Fin MM) (x : Fin VV) : St VV MM :=
  .seq (.op (.copy kS lengthCounter)) (.seq skipNatList (.seq (.op (.copy kD lengthCounter))
    (.seq (.op (.sub kD kS)) (.seq (rewindS kD) (.seq (readListS m) (.op (.copy x lN)))))))

/-- The variables written by `listInto m x`. -/
def listIntoTx (x : Fin VV) : List (Fin VV) := [kS, kD, x] ++ scalarListScratch ++ readListT

/-- The variables written by `listInto m kPc` and `listInto m kFc`. -/
def listIntoT : List (Fin VV) := [kS, kD, kPc, kFc] ++ scalarListScratch ++ readListT

theorem listIntoTx_sub (x : Fin VV) (hx : x ∈ [kPc, kFc]) : ∀ y ∈ listIntoTx x, y ∈ listIntoT := by
  rcases List.mem_cons.mp hx with rfl | h
  · decide
  · simp at h; rw [h]; decide

/-- **Reading a list into a store, counting.** -/
theorem listInto_spec (m : Fin MM) (x : Fin VV) (hx : x ∈ [kPc, kFc]) (a : DS VV MM) (hc : Cst a) (vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = listWord natWord vs ++ rest) (hm : a.ram m = []) (hrc : a.rc m = 0) (L : ℕ)
    (hL : (listWord natWord vs).length ≤ L) (hW : L + 2 ≤ C.Wd)
    (hcap : a.env lengthCounter + (listWord natWord vs).length < 2 ^ C.Wd) :
    Hs C (listInto m x) a (100 * (L + 1) ^ 2 + 6 * L + vs.length * (30 * L + 36) + 30 * L + 62)
      (fun b => b.env x = vs.length ∧ b.ram m = vs ∧ b.rc m = vs.length ∧
        ScannedS a b (listWord natWord vs).length (listIntoTx x) [m] ∧ C.inp.drop b.ip = rest) := by
  have hxl : x ≠ lN := by rcases List.mem_cons.mp hx with rfl | h <;> [decide; (simp at h; rw [h]; decide)]
  have hxT : x ∈ listIntoTx x := by simp [listIntoTx]
  have hxc : x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2 ∧ x ≠ lengthCounter := by
    rcases List.mem_cons.mp hx with rfl | h <;> [decide; (simp at h; rw [h]; decide)]
  set lw := listWord natWord vs with hlw
  refine Hx.hs (Hs.then (hs_copy C kS lengthCounter a (by decide)) (fun b1 hb1 n1 hn1 => ?_))
  subst hb1
  have c1 : Cst (a.set kS (a.env lengthCounter)) := ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩
  have lc1 : (a.set kS (a.env lengthCounter)).env lengthCounter = a.env lengthCounter := DS.set_env_ne _ _ (by decide)
  refine Hs.then (skipNatList_spec C L _ c1 vs rest (by simpa using hin) hL hW (by rw [lc1]; exact hcap))
    (fun b2 s2 n2 hn2 => ?_)
  have s2b : b2.env lengthCounter = (a.set kS (a.env lengthCounter)).env lengthCounter + lw.length := s2.bytes
  have hu2 := s2.unchanged
  simp only [Prod.mk.injEq] at hu2
  refine Hs.then (hs_copy C kD lengthCounter b2 (by decide)) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  have kS2 : b2.env kS = a.env lengthCounter := by
    rw [s2.registers kS (by decide)]; exact DS.set_env_self _ _ _
  refine Hs.then (hs_sub C kD kS _ (by decide) (by
    rw [DS.set_env_self, DS.set_env_ne _ _ (by decide), kS2, s2b, lc1]; omega)) (fun b4 hb4 n4 hn4 => ?_)
  subst hb4
  set b4 := (b2.set kD (b2.env lengthCounter)).set kD ((b2.set kD (b2.env lengthCounter)).env kD -
    (b2.set kD (b2.env lengthCounter)).env kS) with hb4d
  have kD4 : b4.env kD = lw.length := by
    rw [hb4d, DS.set_env_self, DS.set_env_self, DS.set_env_ne _ _ (by decide), kS2, s2b, lc1]; omega
  have c4 : Cst b4 := ⟨by rw [hb4d]; vsimp [s2.constants.z], by rw [hb4d]; vsimp [s2.constants.one],
    by rw [hb4d]; vsimp [s2.constants.two]⟩
  have ip4 : b4.ip = a.ip + lw.length := by rw [hb4d]; simp only [DS.set_ip]; rw [s2.pos]; rfl
  refine Hs.then (rewindS_spec kD (by decide) b4 c4 lw.length kD4 (by rw [ip4]; omega))
    (fun b5 ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, c5⟩ n5 hn5 => ?_)
  have hin5 : C.inp.drop b5.ip = listWord natWord vs ++ rest := by rw [r1, ip4]; simpa using hin
  have hram5 : b5.ram m = [] := by rw [r4, hb4d]; simp only [DS.set_ram]; rw [hu2.2.1]; simpa using hm
  have hrc5 : b5.rc m = 0 := by rw [r5, hb4d]; simp only [DS.set_rc]; rw [hu2.2.2.1]; simpa using hrc
  have hvl : ∀ v ∈ vs.length :: vs, natBitLength v ≤ L := by
    intro v hv
    have h1 : natBitLength v ≤ (natWord v).length := by rw [natWord_length]; omega
    have h2 : (natWord v).length ≤ lw.length := by
      rw [hlw]; unfold listWord
      rcases List.mem_cons.mp hv with rfl | hv
      · simp
      · obtain ⟨l1, l2, hl⟩ := List.append_of_mem hv
        rw [hl, List.flatMap_append, List.flatMap_cons]; simp only [List.length_append]; omega
    omega
  refine Hs.then (readListS_spec_len m b5 c5 vs rest hin5 hram5 hrc5 L hvl hW)
    (fun b6 ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, c6⟩ n6 hn6 => ?_)
  refine Hs.last (hs_copy C x lN b6 hxl) (fun b7 hb7 n7 hn7 => ?_)
  subst hb7
  have hxs : vZ ∉ [x] ∧ v1 ∉ [x] ∧ v2 ∉ [x] := by
    simp only [List.mem_singleton]; exact ⟨fun h => hxc.1 h.symm, fun h => hxc.2.1 h.symm, fun h => hxc.2.2.1 h.symm⟩
  refine ⟨⟨by rw [DS.set_env_self, g0], g1, g2, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Cst.of_fr c6 (Fr.set b6 _
    (List.mem_singleton_self x)) hxs, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [DS.set_ip, g3, r1, ip4, Nat.add_sub_cancel]
  · rw [DS.set_out, g4, r3, hb4d]; simp only [DS.set_out]; rw [hu2.1]; rfl
  · intro m' hm'
    have hm'' : m' ≠ m := fun h => hm' (by simp [h])
    rw [DS.set_ram, (g5 m' hm'').1, r4, hb4d]; simp only [DS.set_ram]; rw [hu2.2.1]; rfl
  · intro m' hm'
    have hm'' : m' ≠ m := fun h => hm' (by simp [h])
    rw [DS.set_rc, (g5 m' hm'').2, r5, hb4d]; simp only [DS.set_rc]; rw [hu2.2.2.1]; rfl
  · rw [DS.set_kin, g6, r6, hb4d]; simp only [DS.set_kin]; rw [hu2.2.2.2.1]; rfl
  · rw [DS.set_kout, g7, r7, hb4d]; simp only [DS.set_kout]; rw [hu2.2.2.2.2.1]; rfl
  · rw [DS.set_kc, g8, r8, hb4d]; simp only [DS.set_kc]; rw [hu2.2.2.2.2.2]; rfl
  · have f1 : Fr a (a.set kS (a.env lengthCounter)) (listIntoTx x) := Fr.set a _ (by simp [listIntoTx])
    have f2 : Fr (a.set kS (a.env lengthCounter)) b2 (listIntoTx x) := s2.registers.weaken (fun y hy => by
      unfold listIntoTx; simp only [List.mem_append]; tauto)
    have f4 : Fr b2 b4 (listIntoTx x) := fun y hy => by
      rw [hb4d, DS.set_env_ne _ _ (fun h => hy (by rw [h]; simp [listIntoTx])),
        DS.set_env_ne _ _ (fun h => hy (by rw [h]; simp [listIntoTx]))]
    have f5 : Fr b4 b5 (listIntoTx x) := r9.weaken (by simp [listIntoTx])
    have f6 : Fr b5 b6 (listIntoTx x) := g9.weaken (fun y hy => by
      unfold listIntoTx; simp only [List.mem_append]; tauto)
    exact f1.trans (f2.trans (f4.trans (f5.trans (f6.trans (Fr.set b6 _ hxT)))))
  · rw [DS.set_env_ne _ _ (fun h => hxc.2.2.2 h.symm), g9 lengthCounter (by decide), r9 lengthCounter (by decide),
      hb4d, DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), s2b, lc1]
  · rw [DS.set_ip, g3, r1, ip4, Nat.add_sub_cancel]; exact drop_step hin
  · have hn2' : n2 ≤ 100 * (L + 1) ^ 2 := hn2
    omega

end NearQuarticWires.Reconstruct
