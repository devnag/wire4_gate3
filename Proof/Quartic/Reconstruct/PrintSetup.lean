import Proof.Quartic.Reconstruct.PrintNest3

/-!
# The constants of the request phase

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`setupA` sets the constants `8`, `128`, `256`, `J + 1` and `2(J+1)` (`setupA_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

/-- The variables written while setting up the request phase. -/
def setupT : List (Fin VV) := [q8, q128, q256, qJp1, qLen, qBase, qO0, qO1, qTop, qA0, qA1, qj, t0, t1, vJ]

/-- The variables written by `setupA`. -/
def setupAT : List (Fin VV) := [q8, q128, q256, qJp1, qLen]

/-- The variables written by `setupB`. -/
def setupBT : List (Fin VV) := [qBase, qO0, vJ]

/-- The variables written by `topS`. -/
def topT : List (Fin VV) := [qTop, qj, t0]

/-- The variables written by `setupC`. -/
def setupCT : List (Fin VV) := [qA0, qA1, qO1]

/-- The constants `8`, `128`, `256`, `J + 1`, `2(J+1)`. -/
def setupA : St VV MM := (.seq (.op (.copy q8 v2)) (.seq (.op (.shl q8)) (.seq (.op (.shl q8)) (.seq (.op (.copy q128 q8)) (.seq (.op (.shl q128)) (.seq (.op (.shl q128)) (.seq (.op (.shl q128)) (.seq (.op (.shl q128)) (.seq (.op (.copy q256 q128)) (.seq (.op (.shl q256)) (.seq (.op (.copy qJp1 kJ)) (.seq (.op (.inc qJp1)) (.seq (.op (.copy qLen qJp1)) (.op (.shl qLen)))))))))))))))

theorem setupA_spec (a : DS VV MM) (hc : Cst a) (J : ℕ) (hJ : a.env kJ = J) (hW : 2 * (J + 1) < 2 ^ C.Wd)
    (h512 : 512 ≤ 2 ^ C.Wd) :
    Hs C setupA a 27 (fun b => b.env q8 = 8 ∧ b.env q128 = 128 ∧ b.env q256 = 256 ∧ b.env qJp1 = J + 1 ∧
      b.env qLen = 2 * (J + 1) ∧ Same a b ∧ Fr a b setupAT) := by
  unfold setupA
  refine Hx.hs (Hs.then (hs_copy C q8 v2 a (by decide)) (fun s1 e1 n1 hn1 => ?_))
  have f1_q8 : s1.env q8 = 2 := by rw [e1, DS.set_env_self, hc.two]
  have f1_kJ : s1.env kJ = J := by rw [e1, DS.set_env_ne _ _ (by decide), hJ]
  have f1_v2 : s1.env v2 = 2 := by rw [e1, DS.set_env_ne _ _ (by decide), hc.two]
  have sm1 : Same a s1 := by rw [e1]; exact Same.set _ _ _
  have fr1 : Fr a s1 setupAT := by rw [e1]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_shl C q8 s1 (by rw [f1_q8]; omega)) (fun s2 e2 n2 hn2 => ?_)
  have f2_q8 : s2.env q8 = (2 * 2) := by rw [e2, DS.set_env_self, f1_q8]
  have f2_kJ : s2.env kJ = J := by rw [e2, DS.set_env_ne _ _ (by decide), f1_kJ]
  have f2_v2 : s2.env v2 = 2 := by rw [e2, DS.set_env_ne _ _ (by decide), f1_v2]
  have sm2 : Same s1 s2 := by rw [e2]; exact Same.set _ _ _
  have fr2 : Fr s1 s2 setupAT := by rw [e2]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_shl C q8 s2 (by rw [f2_q8]; omega)) (fun s3 e3 n3 hn3 => ?_)
  have f3_q8 : s3.env q8 = (2 * (2 * 2)) := by rw [e3, DS.set_env_self, f2_q8]
  have f3_kJ : s3.env kJ = J := by rw [e3, DS.set_env_ne _ _ (by decide), f2_kJ]
  have f3_v2 : s3.env v2 = 2 := by rw [e3, DS.set_env_ne _ _ (by decide), f2_v2]
  have sm3 : Same s2 s3 := by rw [e3]; exact Same.set _ _ _
  have fr3 : Fr s2 s3 setupAT := by rw [e3]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_copy C q128 q8 s3 (by decide)) (fun s4 e4 n4 hn4 => ?_)
  have f4_q128 : s4.env q128 = (2 * (2 * 2)) := by rw [e4, DS.set_env_self, f3_q8]
  have f4_q8 : s4.env q8 = (2 * (2 * 2)) := by rw [e4, DS.set_env_ne _ _ (by decide), f3_q8]
  have f4_kJ : s4.env kJ = J := by rw [e4, DS.set_env_ne _ _ (by decide), f3_kJ]
  have f4_v2 : s4.env v2 = 2 := by rw [e4, DS.set_env_ne _ _ (by decide), f3_v2]
  have sm4 : Same s3 s4 := by rw [e4]; exact Same.set _ _ _
  have fr4 : Fr s3 s4 setupAT := by rw [e4]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_shl C q128 s4 (by rw [f4_q128]; omega)) (fun s5 e5 n5 hn5 => ?_)
  have f5_q128 : s5.env q128 = (2 * (2 * (2 * 2))) := by rw [e5, DS.set_env_self, f4_q128]
  have f5_q8 : s5.env q8 = (2 * (2 * 2)) := by rw [e5, DS.set_env_ne _ _ (by decide), f4_q8]
  have f5_kJ : s5.env kJ = J := by rw [e5, DS.set_env_ne _ _ (by decide), f4_kJ]
  have f5_v2 : s5.env v2 = 2 := by rw [e5, DS.set_env_ne _ _ (by decide), f4_v2]
  have sm5 : Same s4 s5 := by rw [e5]; exact Same.set _ _ _
  have fr5 : Fr s4 s5 setupAT := by rw [e5]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_shl C q128 s5 (by rw [f5_q128]; omega)) (fun s6 e6 n6 hn6 => ?_)
  have f6_q128 : s6.env q128 = (2 * (2 * (2 * (2 * 2)))) := by rw [e6, DS.set_env_self, f5_q128]
  have f6_q8 : s6.env q8 = (2 * (2 * 2)) := by rw [e6, DS.set_env_ne _ _ (by decide), f5_q8]
  have f6_kJ : s6.env kJ = J := by rw [e6, DS.set_env_ne _ _ (by decide), f5_kJ]
  have f6_v2 : s6.env v2 = 2 := by rw [e6, DS.set_env_ne _ _ (by decide), f5_v2]
  have sm6 : Same s5 s6 := by rw [e6]; exact Same.set _ _ _
  have fr6 : Fr s5 s6 setupAT := by rw [e6]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_shl C q128 s6 (by rw [f6_q128]; omega)) (fun s7 e7 n7 hn7 => ?_)
  have f7_q128 : s7.env q128 = (2 * (2 * (2 * (2 * (2 * 2))))) := by rw [e7, DS.set_env_self, f6_q128]
  have f7_q8 : s7.env q8 = (2 * (2 * 2)) := by rw [e7, DS.set_env_ne _ _ (by decide), f6_q8]
  have f7_kJ : s7.env kJ = J := by rw [e7, DS.set_env_ne _ _ (by decide), f6_kJ]
  have f7_v2 : s7.env v2 = 2 := by rw [e7, DS.set_env_ne _ _ (by decide), f6_v2]
  have sm7 : Same s6 s7 := by rw [e7]; exact Same.set _ _ _
  have fr7 : Fr s6 s7 setupAT := by rw [e7]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_shl C q128 s7 (by rw [f7_q128]; omega)) (fun s8 e8 n8 hn8 => ?_)
  have f8_q128 : s8.env q128 = (2 * (2 * (2 * (2 * (2 * (2 * 2)))))) := by rw [e8, DS.set_env_self, f7_q128]
  have f8_q8 : s8.env q8 = (2 * (2 * 2)) := by rw [e8, DS.set_env_ne _ _ (by decide), f7_q8]
  have f8_kJ : s8.env kJ = J := by rw [e8, DS.set_env_ne _ _ (by decide), f7_kJ]
  have f8_v2 : s8.env v2 = 2 := by rw [e8, DS.set_env_ne _ _ (by decide), f7_v2]
  have sm8 : Same s7 s8 := by rw [e8]; exact Same.set _ _ _
  have fr8 : Fr s7 s8 setupAT := by rw [e8]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_copy C q256 q128 s8 (by decide)) (fun s9 e9 n9 hn9 => ?_)
  have f9_q256 : s9.env q256 = (2 * (2 * (2 * (2 * (2 * (2 * 2)))))) := by rw [e9, DS.set_env_self, f8_q128]
  have f9_q8 : s9.env q8 = (2 * (2 * 2)) := by rw [e9, DS.set_env_ne _ _ (by decide), f8_q8]
  have f9_q128 : s9.env q128 = (2 * (2 * (2 * (2 * (2 * (2 * 2)))))) := by rw [e9, DS.set_env_ne _ _ (by decide), f8_q128]
  have f9_kJ : s9.env kJ = J := by rw [e9, DS.set_env_ne _ _ (by decide), f8_kJ]
  have f9_v2 : s9.env v2 = 2 := by rw [e9, DS.set_env_ne _ _ (by decide), f8_v2]
  have sm9 : Same s8 s9 := by rw [e9]; exact Same.set _ _ _
  have fr9 : Fr s8 s9 setupAT := by rw [e9]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_shl C q256 s9 (by rw [f9_q256]; omega)) (fun s10 e10 n10 hn10 => ?_)
  have f10_q256 : s10.env q256 = (2 * (2 * (2 * (2 * (2 * (2 * (2 * 2))))))) := by rw [e10, DS.set_env_self, f9_q256]
  have f10_q8 : s10.env q8 = (2 * (2 * 2)) := by rw [e10, DS.set_env_ne _ _ (by decide), f9_q8]
  have f10_q128 : s10.env q128 = (2 * (2 * (2 * (2 * (2 * (2 * 2)))))) := by rw [e10, DS.set_env_ne _ _ (by decide), f9_q128]
  have f10_kJ : s10.env kJ = J := by rw [e10, DS.set_env_ne _ _ (by decide), f9_kJ]
  have f10_v2 : s10.env v2 = 2 := by rw [e10, DS.set_env_ne _ _ (by decide), f9_v2]
  have sm10 : Same s9 s10 := by rw [e10]; exact Same.set _ _ _
  have fr10 : Fr s9 s10 setupAT := by rw [e10]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_copy C qJp1 kJ s10 (by decide)) (fun s11 e11 n11 hn11 => ?_)
  have f11_qJp1 : s11.env qJp1 = J := by rw [e11, DS.set_env_self, f10_kJ]
  have f11_q8 : s11.env q8 = (2 * (2 * 2)) := by rw [e11, DS.set_env_ne _ _ (by decide), f10_q8]
  have f11_q128 : s11.env q128 = (2 * (2 * (2 * (2 * (2 * (2 * 2)))))) := by rw [e11, DS.set_env_ne _ _ (by decide), f10_q128]
  have f11_q256 : s11.env q256 = (2 * (2 * (2 * (2 * (2 * (2 * (2 * 2))))))) := by rw [e11, DS.set_env_ne _ _ (by decide), f10_q256]
  have f11_kJ : s11.env kJ = J := by rw [e11, DS.set_env_ne _ _ (by decide), f10_kJ]
  have f11_v2 : s11.env v2 = 2 := by rw [e11, DS.set_env_ne _ _ (by decide), f10_v2]
  have sm11 : Same s10 s11 := by rw [e11]; exact Same.set _ _ _
  have fr11 : Fr s10 s11 setupAT := by rw [e11]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_inc C qJp1 s11 (by rw [f11_qJp1]; omega)) (fun s12 e12 n12 hn12 => ?_)
  have f12_qJp1 : s12.env qJp1 = (J + 1) := by rw [e12, DS.set_env_self, f11_qJp1]
  have f12_q8 : s12.env q8 = (2 * (2 * 2)) := by rw [e12, DS.set_env_ne _ _ (by decide), f11_q8]
  have f12_q128 : s12.env q128 = (2 * (2 * (2 * (2 * (2 * (2 * 2)))))) := by rw [e12, DS.set_env_ne _ _ (by decide), f11_q128]
  have f12_q256 : s12.env q256 = (2 * (2 * (2 * (2 * (2 * (2 * (2 * 2))))))) := by rw [e12, DS.set_env_ne _ _ (by decide), f11_q256]
  have f12_kJ : s12.env kJ = J := by rw [e12, DS.set_env_ne _ _ (by decide), f11_kJ]
  have f12_v2 : s12.env v2 = 2 := by rw [e12, DS.set_env_ne _ _ (by decide), f11_v2]
  have sm12 : Same s11 s12 := by rw [e12]; exact Same.set _ _ _
  have fr12 : Fr s11 s12 setupAT := by rw [e12]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_copy C qLen qJp1 s12 (by decide)) (fun s13 e13 n13 hn13 => ?_)
  have f13_qLen : s13.env qLen = (J + 1) := by rw [e13, DS.set_env_self, f12_qJp1]
  have f13_q8 : s13.env q8 = (2 * (2 * 2)) := by rw [e13, DS.set_env_ne _ _ (by decide), f12_q8]
  have f13_q128 : s13.env q128 = (2 * (2 * (2 * (2 * (2 * (2 * 2)))))) := by rw [e13, DS.set_env_ne _ _ (by decide), f12_q128]
  have f13_q256 : s13.env q256 = (2 * (2 * (2 * (2 * (2 * (2 * (2 * 2))))))) := by rw [e13, DS.set_env_ne _ _ (by decide), f12_q256]
  have f13_qJp1 : s13.env qJp1 = (J + 1) := by rw [e13, DS.set_env_ne _ _ (by decide), f12_qJp1]
  have f13_kJ : s13.env kJ = J := by rw [e13, DS.set_env_ne _ _ (by decide), f12_kJ]
  have f13_v2 : s13.env v2 = 2 := by rw [e13, DS.set_env_ne _ _ (by decide), f12_v2]
  have sm13 : Same s12 s13 := by rw [e13]; exact Same.set _ _ _
  have fr13 : Fr s12 s13 setupAT := by rw [e13]; exact Fr.set _ _ (by decide)
  refine Hs.last (hs_shl C qLen s13 (by rw [f13_qLen]; omega)) (fun s14 e14 n14 hn14 => ?_)
  have f14_qLen : s14.env qLen = (2 * (J + 1)) := by rw [e14, DS.set_env_self, f13_qLen]
  have f14_q8 : s14.env q8 = (2 * (2 * 2)) := by rw [e14, DS.set_env_ne _ _ (by decide), f13_q8]
  have f14_q128 : s14.env q128 = (2 * (2 * (2 * (2 * (2 * (2 * 2)))))) := by rw [e14, DS.set_env_ne _ _ (by decide), f13_q128]
  have f14_q256 : s14.env q256 = (2 * (2 * (2 * (2 * (2 * (2 * (2 * 2))))))) := by rw [e14, DS.set_env_ne _ _ (by decide), f13_q256]
  have f14_qJp1 : s14.env qJp1 = (J + 1) := by rw [e14, DS.set_env_ne _ _ (by decide), f13_qJp1]
  have f14_kJ : s14.env kJ = J := by rw [e14, DS.set_env_ne _ _ (by decide), f13_kJ]
  have f14_v2 : s14.env v2 = 2 := by rw [e14, DS.set_env_ne _ _ (by decide), f13_v2]
  have sm14 : Same s13 s14 := by rw [e14]; exact Same.set _ _ _
  have fr14 : Fr s13 s14 setupAT := by rw [e14]; exact Fr.set _ _ (by decide)
  have smA : Same a s14 := (((((((((((((sm1.trans sm2).trans sm3).trans sm4).trans sm5).trans sm6).trans sm7).trans sm8).trans sm9).trans sm10).trans sm11).trans sm12).trans sm13).trans sm14)
  have frA : Fr a s14 setupAT := (((((((((((((fr1.trans fr2).trans fr3).trans fr4).trans fr5).trans fr6).trans fr7).trans fr8).trans fr9).trans fr10).trans fr11).trans fr12).trans fr13).trans fr14)
  exact ⟨⟨by rw [f14_q8], by rw [f14_q128], by rw [f14_q256], by rw [f14_qJp1], by rw [f14_qLen],
    smA, frA⟩, by linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14]⟩

/-- `x := x - 1` (truncated). -/
def decS (x : Fin VV) : St VV MM := .ite (.lt vZ x) (.op (.sub x v1)) (.op (.zero vJ))

theorem decS_spec (x : Fin VV) (hx : x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2 ∧ x ≠ vJ) (a : DS VV MM) (hc : Cst a) :
    Hs C (decS x) a 2 (fun b => b.env x = a.env x - 1 ∧ Same a b ∧ Fr a b [x, vJ] ∧ Cst b) := by
  refine Hs.ite (t := 1) (Ne.symm hx.1) (fun he => ?_) (fun he => ?_)
  · have h : 0 < a.env x := by simpa [Cnd.eval, hc.z] using he
    refine Hs.mono (hs_sub C x v1 a hx.2.1 (by rw [hc.one]; omega)) le_rfl ?_
    rintro b rfl
    refine ⟨by rw [DS.set_env_self, hc.one], Same.set _ _ _, Fr.set _ _ (by simp), Cst.of_fr hc (Fr.set _ _
      (List.mem_singleton_self x)) (by simp only [List.mem_singleton]; exact ⟨fun e => hx.1 e.symm,
        fun e => hx.2.1 e.symm, fun e => hx.2.2.1 e.symm⟩)⟩
  · have h : a.env x = 0 := by simpa [Cnd.eval, hc.z] using he
    refine Hs.mono (hs_zero C vJ a) le_rfl ?_
    rintro b rfl
    refine ⟨by rw [DS.set_env_ne _ _ hx.2.2.2, h], Same.set _ _ _, Fr.set _ _ (by simp),
      ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩⟩

/-- The digit base `2h_E - 1` and the digit shift `h_E - 1`. -/
def setupB : St VV MM :=
  .seq (.op (.copy qBase kE)) (.seq (.op (.shl qBase)) (.seq (decS qBase) (.seq (.op (.copy qO0 kE)) (decS qO0))))

theorem setupB_spec (a : DS VV MM) (hc : Cst a) (hE : ℕ) (hh : a.env kE = hE) (hW : 2 * hE < 2 ^ C.Wd) :
    Hs C setupB a 12 (fun b => b.env qBase = 2 * hE - 1 ∧ b.env qO0 = hE - 1 ∧ Same a b ∧ Fr a b setupBT ∧ Cst b) := by
  refine Hx.hs (Hs.then (hs_copy C qBase kE a (by decide)) (fun b1 e1 n1 hn1 => ?_))
  subst e1
  refine Hs.then (hs_shl C qBase _ (by vsimp [hh]; omega)) (fun b2 e2 n2 hn2 => ?_)
  subst e2
  have c2 : Cst ((a.set qBase (a.env kE)).set qBase (2 * (a.set qBase (a.env kE)).env qBase)) :=
    ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩
  refine Hs.then (decS_spec qBase (by decide) _ c2) (fun b3 ⟨x3, s3, f3, c3⟩ n3 hn3 => ?_)
  refine Hs.then (hs_copy C qO0 kE b3 (by decide)) (fun b4 e4 n4 hn4 => ?_)
  subst e4
  have c4 : Cst (b3.set qO0 (b3.env kE)) := ⟨by vsimp [c3.z], by vsimp [c3.one], by vsimp [c3.two]⟩
  refine Hs.last (decS_spec qO0 (by decide) _ c4) (fun b5 ⟨x5, s5, f5, c5⟩ n5 hn5 => ⟨⟨?_, ?_, ?_, ?_, c5⟩, by omega⟩)
  · rw [f5 qBase (by decide), DS.set_env_ne _ _ (by decide), x3]; vsimp [hh]
  · rw [x5, DS.set_env_self, f3 kE (by decide)]; vsimp [hh]
  · exact (((Same.set _ _ _).trans (Same.set _ _ _)).trans s3).trans ((Same.set _ _ _).trans s5)
  · exact (((Fr.set a _ (by decide)).trans (Fr.set _ _ (by decide))).trans (f3.weaken (by decide))).trans
      ((Fr.set _ _ (by decide)).trans (f5.weaken (by decide)))

/-- `B^J`: multiply `J` times. -/
def topS : St VV MM := .seq (.op (.copy qTop v1)) (forS qj kJ (.seq (.op (.mul qTop qBase t0)) (.op (.copy qTop t0))))

theorem topS_spec (a : DS VV MM) (hc : Cst a) (B J : ℕ) (hB : a.env qBase = B) (hJ : a.env kJ = J)
    (hW : B ^ J < 2 ^ C.Wd) (hJW : J < 2 ^ C.Wd) :
    Hs C topS a (1 + (J * (3 + 4) + 4) + 1) (fun b => b.env qTop = B ^ J ∧ Same a b ∧ Fr a b topT ∧ Cst b) := by
  refine Hx.hs (Hs.then (hs_copy C qTop v1 a (by decide)) (fun b0 e0 n0 hn0 => ?_))
  subst e0
  let Inv : ℕ → DS VV MM → Prop := fun j c => c.env qTop = B ^ j ∧ c.env qBase = B ∧ Same a c ∧ Fr a c topT ∧ Cst c
  have hset : ∀ j c v, Inv j c → Inv j (c.set qj v) := fun j c v ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨by rw [DS.set_env_ne _ _ (by decide), h1], by rw [DS.set_env_ne _ _ (by decide), h2], h3.trans (Same.set _ _ _),
      h4.trans (Fr.set _ _ (by decide)), ⟨by vsimp [h5.z], by vsimp [h5.one], by vsimp [h5.two]⟩⟩
  have hpow : ∀ j, j ≤ J → B ^ j ≤ B ^ J ∨ B = 0 := fun j hj => by
    rcases Nat.eq_zero_or_pos B with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.pow_le_pow_right h hj)
  refine Hs.last (forS_spec qj kJ (by decide) _ J 3 (fun _ => []) Inv hset ?_ _
    ⟨by vsimp [hc.one], by vsimp [hB], Same.set _ _ _, Fr.set _ _ (by decide),
      ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩⟩ (by vsimp [hJ]) hJW)
    (fun b ⟨⟨b1, _, b3, b4, b5⟩, _, _⟩ n hn => ⟨⟨b1, b3, b4, b5⟩, by omega⟩)
  intro j hj c ⟨h1, h2, h3, h4, h5⟩ hjj hnj
  have hle : B ^ (j + 1) < 2 ^ C.Wd := by
    rcases hpow (j + 1) (by omega) with h | h
    · omega
    · rw [h, zero_pow (by omega)]; omega
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_mul C qTop qBase t0 c (by decide) (by decide) (by decide)
    (by rw [h1, h2, ← pow_succ]; exact hle)) (fun d1 e1 => ?_)
  subst e1
  refine Hs.mono (hs_copy C qTop t0 _ (by decide)) le_rfl ?_
  rintro d rfl
  refine ⟨⟨by vsimp [h1, h2]; ring, by vsimp [h2], h3.trans ((Same.set _ _ _).trans (Same.set _ _ _)),
    h4.trans ((Fr.set _ _ (by decide)).trans (Fr.set _ _ (by decide))),
    ⟨by vsimp [h5.z], by vsimp [h5.one], by vsimp [h5.two]⟩⟩, by vsimp [hjj], by vsimp [hnj], by vsimp []⟩

/-- The numbers of digit vectors and the shift of the second circuit. -/
def setupC : St VV MM :=
  .seq (.op (.mul qTop qBase qA0)) (.ite (.eq kPair v1) (.seq (.op (.copy qA1 qA0)) (.op (.copy qO1 qO0)))
    (.seq (.op (.copy qA1 v1)) (.op (.zero qO1))))

theorem setupC_spec (a : DS VV MM) (hc : Cst a) (T B o pb : ℕ) (hT : a.env qTop = T) (hB : a.env qBase = B)
    (ho : a.env qO0 = o) (hpb : a.env kPair = pb) (hW : T * B < 2 ^ C.Wd) :
    Hs C setupC a 6 (fun b => b.env qA0 = T * B ∧ b.env qA1 = (if pb = 1 then T * B else 1) ∧
      b.env qO1 = (if pb = 1 then o else 0) ∧ Same a b ∧ Fr a b setupCT ∧ Cst b) := by
  refine Hx.hs (Hs.then (hs_mul C qTop qBase qA0 a (by decide) (by decide) (by decide) (by rw [hT, hB]; exact hW))
    (fun b1 e1 n1 hn1 => ?_))
  subst e1
  have c1 : Cst (a.set qA0 (a.env qTop * a.env qBase)) := ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩
  have ep : (a.set qA0 (a.env qTop * a.env qBase)).env kPair = pb := by rw [DS.set_env_ne _ _ (by decide), hpb]
  refine Hs.last (Hs.ite (t := 3) (show kPair ≠ v1 by decide) (fun he => ?_) (fun he => ?_))
    (fun b hb n hn => ⟨hb, by omega⟩)
  · have h1 : pb = 1 := by simpa [Cnd.eval, ep, c1.one] using he
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C qA1 qA0 _ (by decide)) (fun d e => ?_)
    subst e
    refine Hs.mono (hs_copy C qO1 qO0 _ (by decide)) le_rfl ?_
    rintro b rfl
    refine ⟨by vsimp [hT, hB], by vsimp [hT, hB, h1], by vsimp [ho, h1],
      ((Same.set _ _ _).trans (Same.set _ _ _)).trans (Same.set _ _ _),
      ((Fr.set _ _ (by decide)).trans (Fr.set _ _ (by decide))).trans (Fr.set _ _ (by decide)),
      ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩⟩
  · have h1 : pb ≠ 1 := by simpa [Cnd.eval, ep, c1.one] using he
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C qA1 v1 _ (by decide)) (fun d e => ?_)
    subst e
    refine Hs.mono (hs_zero C qO1 _) le_rfl ?_
    rintro b rfl
    refine ⟨by vsimp [hT, hB], by vsimp [hc.one, h1], by vsimp [h1],
      ((Same.set _ _ _).trans (Same.set _ _ _)).trans (Same.set _ _ _),
      ((Fr.set _ _ (by decide)).trans (Fr.set _ _ (by decide))).trans (Fr.set _ _ (by decide)),
      ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩⟩

/-- The number of printed tables. -/
def qCnt : Fin VV := ⟨46, by decide⟩

/-- `512 · A_0 · A_1 · (tables per group)`. -/
def countS : St VV MM :=
  .seq (.op (.copy qCnt q256)) (.seq (.op (.shl qCnt)) (.seq (.op (.mul qCnt qA0 t0)) (.seq (.op (.mul t0 qA1 t1))
    (.op (.mul t1 kG qCnt)))))

theorem countS_spec (a : DS VV MM) (hc : Cst a) (A0 A1 tg : ℕ) (h256 : a.env q256 = 256) (h0 : a.env qA0 = A0)
    (h1 : a.env qA1 = A1) (hg : a.env kG = tg) (hW : 512 * A0 * A1 * tg < 2 ^ C.Wd) (hW1 : 512 * A0 * A1 < 2 ^ C.Wd)
    (hW0 : 512 * A0 < 2 ^ C.Wd) (h512 : 512 < 2 ^ C.Wd) :
    Hs C countS a 9 (fun b => b.env qCnt = 512 * A0 * A1 * tg ∧ Same a b ∧ Fr a b [qCnt, t0, t1] ∧ Cst b) := by
  refine Hx.hs (Hs.then (hs_copy C qCnt q256 a (by decide)) (fun b1 e1 n1 hn1 => ?_))
  subst e1
  refine Hs.then (hs_shl C qCnt _ (by vsimp [h256]; omega)) (fun b2 e2 n2 hn2 => ?_)
  subst e2
  refine Hs.then (hs_mul C qCnt qA0 t0 _ (by decide) (by decide) (by decide) (by vsimp [h256, h0]; omega))
    (fun b3 e3 n3 hn3 => ?_)
  subst e3
  refine Hs.then (hs_mul C t0 qA1 t1 _ (by decide) (by decide) (by decide) (by vsimp [h256, h0, h1]; omega))
    (fun b4 e4 n4 hn4 => ?_)
  subst e4
  refine Hs.last (hs_mul C t1 kG qCnt _ (by decide) (by decide) (by decide) (by vsimp [h256, h0, h1, hg]; omega))
    (fun b5 e5 n5 hn5 => ⟨⟨?_, ?_, ?_, ?_⟩, by omega⟩)
  · subst e5; vsimp [h256, h0, h1, hg]
  · subst e5
    exact (((((Same.set _ _ _).trans (Same.set _ _ _)).trans (Same.set _ _ _)).trans (Same.set _ _ _)).trans
      (Same.set _ _ _))
  · subst e5
    exact (((((Fr.set a _ (by decide)).trans (Fr.set _ _ (by decide))).trans (Fr.set _ _ (by decide))).trans
      (Fr.set _ _ (by decide))).trans (Fr.set _ _ (by decide)))
  · subst e5; exact ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩

end NearQuarticWires.Reconstruct
