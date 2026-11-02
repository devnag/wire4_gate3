import Proof.Quartic.Reconstruct.PrintFrame

/-!
# Rewinding the input and copying a counted number of bits

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

* `rewindS x`: move the input cursor back by the number held in `x` (`rewindS_spec`);
* `rawCopyS m x`: copy as many input bits as `x` holds into store `m` (`rawCopyS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

/-- Move the input cursor back by `x` bits. -/
def rewindS (x : Fin VV) : St VV MM := .loop (.lt vZ x) (.seq (.op .bkI) (.op (.sub x v1)))

/-- Copy `x` input bits into store `m`. -/
def rawCopyS (m : Fin MM) (x : Fin VV) : St VV MM :=
  .loop (.lt vZ x) (.seq (.op (.rdI fB)) (.seq (.op (.wrM m fB)) (.op (.sub x v1))))

/-- **Rewinding the input.** -/
theorem rewindS_spec (x : Fin VV) (hx : x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2) (a : DS VV MM) (hc : Cst a) (k : ℕ)
    (hk : a.env x = k) (hip : k ≤ a.ip) :
    Hs C (rewindS x) a (k * 5 + 2) (fun b => b.ip = a.ip - k ∧ b.env x = 0 ∧ b.out = a.out ∧ b.ram = a.ram ∧
      b.rc = a.rc ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [x] ∧ Cst b) := by
  have hT : vZ ∉ [x] ∧ v1 ∉ [x] ∧ v2 ∉ [x] := by
    simp only [List.mem_singleton]; exact ⟨fun h => hx.1 h.symm, fun h => hx.2.1 h.symm, fun h => hx.2.2 h.symm⟩
  let I : ℕ → DS VV MM → Prop := fun j b => b.env x = k - j ∧ b.ip = a.ip - j ∧ b.out = a.out ∧ b.ram = a.ram ∧
    b.rc = a.rc ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [x] ∧ Cst b
  refine (Hs.loopN (c := .lt vZ x) (Ne.symm hx.1) I k 3 ?_ ?_ a ⟨by rw [hk]; rfl, by simp, rfl, rfl, rfl, rfl, rfl,
    rfl, Fr.refl a _, hc⟩).mono (by omega) (fun b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => ⟨h2, by omega, h3, h4,
      h5, h6, h7, h8, h9, h10⟩)
  · intro j hj b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    refine ⟨by simp [Cnd.eval, h1, h10.z]; omega, ?_⟩
    refine Hs.seq (t1 := 1) (t2 := 1) (Hs.op (OpEx.bkI b (by omega)) rfl) (fun b1 hb1 => ?_)
    subst hb1
    refine Hs.mono (hs_sub C x v1 _ hx.2.1 (by show b.env v1 ≤ b.env x; rw [h10.one, h1]; omega)) le_rfl ?_
    rintro c rfl
    refine ⟨?_, by simp only [DS.set_ip]; show b.ip - 1 = _; omega, h3, h4, h5, h6, h7, h8, ?_, ?_⟩
    · show (DS.set { b with ip := b.ip - 1 } x (b.env x - b.env v1)).env x = _
      rw [DS.set_env_self, h1, h10.one]; omega
    · exact Fr.trans h9 (fun y hy => DS.set_env_ne _ _ (by simpa using hy))
    · exact Cst.of_fr h10 (fun y hy => DS.set_env_ne _ _ (by simpa using hy)) hT
  · intro b ⟨h1, _, _, _, _, _, _, _, _, h10⟩
    simp [Cnd.eval, h1, h10.z]

/-- **Copying a counted number of bits.** -/
theorem rawCopyS_spec (m : Fin MM) (x : Fin VV) (hx : x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2 ∧ x ≠ fB) (a : DS VV MM)
    (hc : Cst a) (w rest : List Bool) (hk : a.env x = w.length) (hin : C.inp.drop a.ip = w ++ rest)
    (hend : a.rc m = (a.ram m).length) :
    Hs C (rawCopyS m x) a (w.length * 7 + 2) (fun b => InMoved a b m w.length (w.map Bool.toNat) [fB, x] ∧
      C.inp.drop b.ip = rest ∧ b.env x = 0 ∧ Cst b) := by
  have hT : vZ ∉ [fB, x] ∧ v1 ∉ [fB, x] ∧ v2 ∉ [fB, x] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨by decide, fun h => hx.1 h.symm⟩, ⟨by decide, fun h => hx.2.1 h.symm⟩, ⟨by decide, fun h => hx.2.2.1 h.symm⟩⟩
  let I : ℕ → DS VV MM → Prop := fun j b => b.env x = w.length - j ∧ C.inp.drop b.ip = w.drop j ++ rest ∧
    InMoved a b m j ((w.take j).map Bool.toNat) [fB, x] ∧ b.rc m = (b.ram m).length ∧ Cst b
  refine (Hs.loopN (c := .lt vZ x) (Ne.symm hx.1) I w.length 5 ?_ ?_ a ⟨by rw [hk]; rfl, by simpa using hin,
    by simpa using InMoved.refl a m [fB, x], hend, hc⟩).mono (by omega)
      (fun b ⟨h1, h2, h3, _, h5⟩ => ⟨by rwa [List.take_length] at h3, by simpa using h2, by omega, h5⟩)
  · intro j hj b ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by simp [Cnd.eval, h1, h5.z]; omega, ?_⟩
    have hd : w.drop j = w[j] :: w.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [hd] at h2
    refine Hx.hs (Hs.then (rdI_spec' fB m b w[j] _ h2) (fun b1 ⟨x1, d1, m1⟩ n1 hn1 => ?_))
    refine Hs.then (wrM_spec' m fB b1 (m1.endc h4)) (fun b2 ⟨m2, ev2⟩ n2 hn2 => ?_)
    have c1 := m1.cst h5 (by decide)
    have c2 : Cst b2 := ⟨by rw [ev2]; exact c1.z, by rw [ev2]; exact c1.one, by rw [ev2]; exact c1.two⟩
    have ex2 : b2.env x = w.length - j := by
      rw [ev2, m1.fr x (by simp only [List.mem_singleton]; exact hx.2.2.2), h1]
    refine Hs.last (hs_sub C x v1 b2 hx.2.1 (by rw [c2.one, ex2]; omega)) (fun b3 hb3 n3 hn3 => ⟨?_, by omega⟩)
    subst hb3
    have hxs : vZ ∉ [x] ∧ v1 ∉ [x] ∧ v2 ∉ [x] := by
      simp only [List.mem_singleton]
      exact ⟨fun h => hx.1 h.symm, fun h => hx.2.1 h.symm, fun h => hx.2.2.1 h.symm⟩
    refine ⟨by rw [DS.set_env_self, ex2, c2.one]; omega, by simp only [DS.set_ip]; rw [m2.ip, Nat.add_zero, d1]; rfl,
      ?_, by simp only [DS.set_rc, DS.set_ram]; exact m2.endc (m1.endc h4),
      Cst.of_fr c2 (Fr.set b2 _ (List.mem_singleton_self x)) hxs⟩
    have mv := ((h3.trans (m1.weaken (by simp))).trans (m2.weaken (by simp))).set (b2.env x - b2.env v1)
      (show x ∈ [fB, x] by simp)
    rw [x1] at mv
    rw [List.take_succ_eq_append_getElem hj, List.map_append]
    simpa using mv
  · intro b ⟨h1, _, _, _, h5⟩
    simp [Cnd.eval, h1, h5.z]

end NearQuarticWires.Reconstruct
