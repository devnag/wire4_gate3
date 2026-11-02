import Proof.Quartic.Reconstruct.PrintCtxRun

/-!
# Writing the digits of a counter

Paper: Step 3 of `sec:algorithm`, paper/paper.tex (the index of a printed table carries the pattern
`σ` and the digit vector `δ`, enumerated by counters, `PrintEnum.vecList_eq_range`).

`digLoopS X base cnt em` writes, for `j = 0, …, N - 1`, the digit `(x / base^(N-1-j)) % base` of the number `x` held in
`X` through the writer `em` (which writes from `qDg`), keeping the power `base^(N-1-j)` in `qPw` (`digLoopS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

/-- The power of the base. -/
def qPw : Fin VV := ⟨20, by decide⟩
/-- A quotient. -/
def qQ : Fin VV := ⟨21, by decide⟩
/-- The digit. -/
def qDg : Fin VV := ⟨22, by decide⟩
/-- The digit index. -/
def qj : Fin VV := ⟨23, by decide⟩

/-- Write the digits of `X` in base `base` (`cnt` digits, the power `base^(cnt-1)` in `qPw`). -/
def digLoopS (X base cnt : Fin VV) (em : St VV MM) : St VV MM :=
  forS qj cnt (.seq (.op (.dm X qPw qQ t0)) (.seq (.op (.dm qQ base t1 qDg)) (.seq em
    (.seq (.op (.dm qPw base qQ t0)) (.op (.copy qPw qQ))))))

/-- The variables written by the body of `digLoopS` besides those of `em`. -/
def digT : List (Fin VV) := [qPw, qQ, qDg, qj, t0, t1]

theorem pow_div_base (base e : ℕ) (hb : 0 < base) : base ^ (e + 1) / base = base ^ e := by
  rw [pow_succ, Nat.mul_div_cancel _ hb]

/-- **Writing the digits of a counter.** -/
theorem digLoopS_spec (X base cnt : Fin VV) (em : St VV MM) (wf : ℕ → List Bool) (Tem : List (Fin VV)) (te : ℕ)
    (hv : ∀ y ∈ [X, base, cnt], y ∉ digT ∧ y ∉ Tem)
    (hTem : qj ∉ Tem ∧ qPw ∉ Tem) (hc0 : vZ ∉ Tem ∧ v1 ∉ Tem ∧ v2 ∉ Tem)
    (x b N : ℕ) (hb : 0 < b)
    (a : DS VV MM)
    (hem : ∀ c : DS VV MM, Cst c → (∀ m, c.rc m ≤ (c.ram m).length) → c.env qDg < b → Fr a c (digT ++ Tem) →
      Hs C em c te (fun d => OutMoved c d (wf (c.env qDg)) Tem ∧ d.rc = c.rc ∧ Cst d)) (hc : Cst a) (hok : ∀ m, a.rc m ≤ (a.ram m).length) (hx : a.env X = x) (hbb : a.env base = b)
    (hn : a.env cnt = N) (hpw : a.env qPw = b ^ (N - 1)) (hbW : 2 * b ^ N ≤ 2 ^ C.Wd) (hNW : N < 2 ^ C.Wd) :
    Hs C (digLoopS X base cnt em) a (N * (te + 4 + 4 + 4) + 4)
      (fun c => OutMoved a c ((List.range N).flatMap fun j => wf ((x / b ^ (N - 1 - j)) % b)) (digT ++ Tem) ∧
        Cst c) := by
  set T := digT ++ Tem with hT
  have hcT : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T := by
    simp only [hT, List.mem_append, not_or]; exact ⟨⟨by decide, hc0.1⟩, ⟨by decide, hc0.2.1⟩, ⟨by decide, hc0.2.2⟩⟩
  have hvT : ∀ y ∈ [X, base, cnt], y ∉ T := fun y hy => by
    simp only [hT, List.mem_append, not_or]; exact hv y hy
  let Inv : ℕ → DS VV MM → Prop := fun j c => Cst c ∧ (j < N → c.env qPw = b ^ (N - 1 - j)) ∧
    c.env X = x ∧ c.env base = b ∧ c.ram = a.ram ∧ c.ip = a.ip ∧ c.kin = a.kin ∧ c.kout = a.kout ∧ c.kc = a.kc ∧
    Fr a c T ∧ (∀ m, c.rc m ≤ (c.ram m).length)
  have hset : ∀ j c v, Inv j c → Inv j (c.set qj v) := fun j c v ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ =>
    ⟨Cst.of_fr h1 (Fr.set c v (List.mem_singleton_self qj)) (by decide),
      fun h => by rw [DS.set_env_ne _ _ (by decide), h2 h],
      by rw [DS.set_env_ne _ _ (fun h => (hv X (by simp)).1 (by rw [h]; decide)), h3],
      by rw [DS.set_env_ne _ _ (fun h => (hv base (by simp)).1 (by rw [h]; decide)), h4],
      h5, h6, h7, h8, h9, Fr.trans h10 (Fr.set c v (by simp [hT, digT])), h11⟩
  have hbN : ∀ e, e ≤ N → b ^ e ≤ b ^ N := fun e he => Nat.pow_le_pow_right hb he
  refine (forS_spec qj cnt (fun h => (hv cnt (by simp)).1 (by rw [← h]; decide)) _ N (te + 4 + 4)
    (fun j => wf ((x / b ^ (N - 1 - j)) % b)) Inv hset ?_ a
    ⟨hc, fun _ => by rw [hpw]; congr 1, hx, hbb, rfl, rfl, rfl, rfl, rfl, Fr.refl a T, hok⟩ hn hNW).mono le_rfl
    (fun c ⟨⟨c1, _, _, _, c5, c6, c7, c8, c9, c10, c11⟩, _, c12⟩ => ⟨⟨c12, c6, c5, c7, c8, c9, c10, c11⟩, c1⟩)
  intro j hj c ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ hjj hnj
  have hpj := h2 hj
  have hpos : 0 < b ^ (N - 1 - j) := pow_pos hb _
  have hle : b ^ (N - 1 - j) ≤ b ^ N := hbN _ (by omega)
  have hb1 : b ≤ b ^ N := by
    calc b = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ N := Nat.pow_le_pow_right hb (by omega)
  have nX : X ≠ qPw ∧ X ≠ qQ ∧ X ≠ qDg ∧ X ≠ qj ∧ X ≠ t0 ∧ X ≠ t1 := by
    have := (hv X (by simp)).1; simp only [digT, List.mem_cons, List.not_mem_nil, or_false, not_or] at this; tauto
  have nB : base ≠ qPw ∧ base ≠ qQ ∧ base ≠ qDg ∧ base ≠ qj ∧ base ≠ t0 ∧ base ≠ t1 := by
    have := (hv base (by simp)).1; simp only [digT, List.mem_cons, List.not_mem_nil, or_false, not_or] at this; tauto
  have nC : cnt ≠ qPw ∧ cnt ≠ qQ ∧ cnt ≠ qDg ∧ cnt ≠ qj ∧ cnt ≠ t0 ∧ cnt ≠ t1 := by
    have := (hv cnt (by simp)).1; simp only [digT, List.mem_cons, List.not_mem_nil, or_false, not_or] at this; tauto
  refine Hx.hs (Hs.then (hs_dm C X qPw qQ t0 c nX.1 nX.2.1 nX.2.2.2.2.1 (by decide) (by decide) (by decide)
    (by rw [hpj]; exact hpos) (by rw [hpj]; omega)) (fun c1 e1 n1 hn1 => ?_))
  have c1Q : c1.env qQ = x / b ^ (N - 1 - j) := by rw [e1]; vsimp [hpj, h3]
  have c1B : c1.env base = b := by rw [e1, DS.set_env_ne _ _ nB.2.2.2.2.1, DS.set_env_ne _ _ nB.2.1, h4]
  refine Hs.then (hs_dm C qQ base t1 qDg c1 (Ne.symm nB.2.1) (by decide) (by decide) nB.2.2.2.2.2 nB.2.2.1 (by decide)
    (by rw [c1B]; exact hb) (by rw [c1B]; omega)) (fun c2 e2 n2 hn2 => ?_)
  have c2D : c2.env qDg = (x / b ^ (N - 1 - j)) % b := by rw [e2, DS.set_env_self, c1Q, c1B]
  have hcst2 : Cst c2 := ⟨by rw [e2, e1]; vsimp [h1.z], by rw [e2, e1]; vsimp [h1.one], by rw [e2, e1]; vsimp [h1.two]⟩
  have hok2 : ∀ m, c2.rc m ≤ (c2.ram m).length := fun m => by rw [e2, e1]; exact h11 m
  have fr2 : Fr a c2 T := fun y hy => by
    have hy1 : y ∉ digT := fun h => hy (List.mem_append_left _ h)
    simp only [digT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy1
    rw [e2, DS.set_env_ne _ _ hy1.2.2.1, DS.set_env_ne _ _ hy1.2.2.2.2.2, e1, DS.set_env_ne _ _ hy1.2.2.2.2.1,
      DS.set_env_ne _ _ hy1.2.1]
    exact h10 y hy
  refine Hs.then (hem c2 hcst2 hok2 (by rw [c2D]; exact Nat.mod_lt _ hb) fr2) (fun c3 ⟨m3, r3, cc3⟩ n3 hn3 => ?_)
  have k23 : ∀ y, y ∉ Tem → c3.env y = c2.env y := m3.fr
  have c3P : c3.env qPw = b ^ (N - 1 - j) := by
    rw [k23 qPw hTem.2, e2, DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), e1,
      DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), hpj]
  have c3B : c3.env base = b := by
    rw [k23 base (hv base (by simp)).2, e2, DS.set_env_ne _ _ nB.2.2.1, DS.set_env_ne _ _ nB.2.2.2.2.2, c1B]
  refine Hs.then (hs_dm C qPw base qQ t0 c3 (Ne.symm nB.1) (by decide) (by decide) nB.2.1 nB.2.2.2.2.1 (by decide)
    (by rw [c3B]; exact hb) (by rw [c3B]; omega)) (fun c4 e4 n4 hn4 => ?_)
  refine Hs.last (hs_copy C qPw qQ c4 (by decide)) (fun c5 e5 n5 hn5 => ⟨⟨?_, ?_, ?_, ?_⟩, by omega⟩)
  · -- the invariant
    have k5 : ∀ y, y ∉ T → c5.env y = c.env y := by
      intro y hy
      have hy1 : y ∉ digT := fun h => hy (List.mem_append_left _ h)
      have hy2 : y ∉ Tem := fun h => hy (List.mem_append_right _ h)
      simp only [digT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy1
      rw [e5, DS.set_env_ne _ _ hy1.1, e4, DS.set_env_ne _ _ hy1.2.2.2.2.1, DS.set_env_ne _ _ hy1.2.1, k23 y hy2, e2,
        DS.set_env_ne _ _ hy1.2.2.1, DS.set_env_ne _ _ hy1.2.2.2.2.2, e1, DS.set_env_ne _ _ hy1.2.2.2.2.1,
        DS.set_env_ne _ _ hy1.2.1]
    refine ⟨?_, fun h => ?_, by rw [k5 X (hvT X (by simp)), h3], by rw [k5 base (hvT base (by simp)), h4], ?_, ?_, ?_, ?_,
      ?_, fun y hy => (k5 y hy).trans (h10 y hy), fun m => ?_⟩
    · rw [e5, e4]; exact ⟨by vsimp [cc3.z], by vsimp [cc3.one], by vsimp [cc3.two]⟩
    · rw [e5, DS.set_env_self, e4, DS.set_env_ne _ _ (by decide), DS.set_env_self, c3P, c3B]
      have : N - 1 - j = (N - 1 - (j + 1)) + 1 := by omega
      rw [this, pow_div_base _ _ hb]
    · rw [e5, e4]; simp only [DS.set_ram]; rw [m3.ram, e2, e1]; simp only [DS.set_ram]; exact h5
    · rw [e5, e4]; simp only [DS.set_ip]; rw [m3.ip, e2, e1]; simp only [DS.set_ip]; exact h6
    · rw [e5, e4]; simp only [DS.set_kin]; rw [m3.kin, e2, e1]; simp only [DS.set_kin]; exact h7
    · rw [e5, e4]; simp only [DS.set_kout]; rw [m3.kout, e2, e1]; simp only [DS.set_kout]; exact h8
    · rw [e5, e4]; simp only [DS.set_kc]; rw [m3.kc, e2, e1]; simp only [DS.set_kc]; exact h9
    · rw [e5, e4]; simp only [DS.set_rc, DS.set_ram]; exact m3.rcok m
  · rw [e5, DS.set_env_ne _ _ (by decide), e4, DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide),
      k23 qj hTem.1, e2, DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), e1,
      DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), hjj]
  · rw [e5, DS.set_env_ne _ _ nC.1, e4, DS.set_env_ne _ _ nC.2.2.2.2.1, DS.set_env_ne _ _ nC.2.1,
      k23 cnt (hv cnt (by simp)).2, e2, DS.set_env_ne _ _ nC.2.2.1, DS.set_env_ne _ _ nC.2.2.2.2.2, e1,
      DS.set_env_ne _ _ nC.2.2.2.2.1, DS.set_env_ne _ _ nC.2.1, hnj]
  · rw [e5, e4]; simp only [DS.set_out]; rw [m3.out, c2D, e2, e1]; simp only [DS.set_out]

end NearQuarticWires.Reconstruct
