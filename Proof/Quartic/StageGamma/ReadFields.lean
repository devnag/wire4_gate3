import Proof.Gates.Cells.Kit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: decode a
source natural into its designated binary variable. -/
def readField (x : Fin VV) : St VV MM := .seq rdNatI (.op (.copy x t3))

/-- `cor:conditional`, paper/paper.tex: one decoded
field preserves all previously stored source fields outside its scratch. -/
theorem readField_spec (C : Ctx) (x : Fin VV) (hx : x ∉ [vZ, v1, v2]) (hxt : x ≠ t3)
    (a : DS VV MM) (hc : Cst a) (v : ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = natWord v ++ rest) (hW : natBitLength v + 2 ≤ C.Wd) :
    Hs C (readField x) a (30 * natBitLength v + 32) (fun b =>
      b.env x = v ∧ b.ip = a.ip + (natWord v).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b (x :: rdNatT)) := by
  unfold readField
  refine Hs.mono (Hs.seq (t2 := 1) (rdNatI_spec a hc v rest hin hW) (fun b hb => ?_))
    (by omega) (fun _ h => h)
  obtain ⟨hv, _, hip, hrest, hfr⟩ := hb
  refine Hs.mono (hs_copy C x t3 b hxt) le_rfl ?_
  rintro e rfl
  refine ⟨by simpa using hv, hip, hrest, ?_, ?_⟩
  · have hbc : Cst b := cst_fr hc hfr
    have hxZ : vZ ≠ x := by intro h; exact hx (by simp [← h])
    have hx1 : v1 ≠ x := by intro h; exact hx (by simp [← h])
    have hx2 : v2 ≠ x := by intro h; exact hx (by simp [← h])
    exact ⟨by rw [DS.set_env_ne _ _ hxZ]; exact hbc.z,
      by rw [DS.set_env_ne _ _ hx1]; exact hbc.one,
      by rw [DS.set_env_ne _ _ hx2]; exact hbc.two⟩
  · exact Fr.trans (Fr.weaken hfr (by intro y hy; simp [hy])) (Fr.set b _ (by simp))

/-- `cor:conditional`, paper/paper.tex: a fixed
finite sequence of input-field readers. -/
def readFields : List (Fin VV) → St VV MM
  | [] => skipS
  | x :: xs => .seq (readField x) (readFields xs)

/-- `prop:time`, paper/paper.tex: the source parser's
cost depends on the actual binary field lengths. -/
def readFieldsCost : List ℕ → ℕ
  | [] => 1
  | v :: vs => 30 * natBitLength v + 33 + readFieldsCost vs

/-- `prop:time`, paper/paper.tex: bounded binary field
lengths give a concrete linear bound on the input parser's execution. -/
theorem readFieldsCost_le (vs : List ℕ) (L : ℕ)
    (h : ∀ v ∈ vs, natBitLength v ≤ L) :
    readFieldsCost vs ≤ vs.length * (30 * L + 33) + 1 := by
  induction vs with
  | nil => simp [readFieldsCost]
  | cons v vs ih =>
    have hv := h v (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [readFieldsCost, List.length_cons]
    nlinarith

/-- `cor:conditional`, paper/paper.tex: every fixed
source field is decoded once, with the exact cursor movement. -/
theorem readFields_spec (C : Ctx) (xs : List (Fin VV))
    (hn : xs.Nodup) (hsafe : ∀ x ∈ xs, x ∉ vJ :: rdNatT ∧ x ∉ [vZ, v1, v2])
    (vs : List ℕ) (hlen : xs.length = vs.length) (a : DS VV MM) (hc : Cst a)
    (rest : List Bool) (hin : C.inp.drop a.ip = vs.flatMap natWord ++ rest)
    (hW : ∀ v ∈ vs, natBitLength v + 2 ≤ C.Wd) :
    Hs C (readFields xs) a (readFieldsCost vs) (fun b =>
      (∀ i : Fin xs.length, b.env xs[i] = vs[i.val]'(by omega)) ∧
      b.ip = a.ip + (vs.flatMap natWord).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b (xs ++ vJ :: rdNatT)) := by
  induction xs generalizing vs a with
  | nil =>
    have hv : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst hv
    refine Hs.mono (skip_spec a) le_rfl ?_
    rintro b rfl
    refine ⟨fun i => i.elim0, by simp [DS.set], rfl, ?_, ?_⟩
    · exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two⟩
    · exact Fr.set a _ (by simp)
  | cons x xs ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      have hnd : x ∉ xs ∧ xs.Nodup := by simpa using hn
      have hx := hsafe x (by simp)
      have hxt : x ≠ t3 := by intro h; exact hx.1 (by simp [h, rdNatT])
      refine Hs.mono (Hs.seq (t2 := readFieldsCost vs) (readField_spec C x hx.2 hxt a hc v
        (vs.flatMap natWord ++ rest) (by simpa [List.append_assoc] using hin)
        (hW v (by simp))) (fun b ⟨hb, hip, hrest, hbc, hfr⟩ => ?_))
        (by dsimp [readFieldsCost]; omega) (fun _ h => h)
      have hin' : C.inp.drop b.ip = vs.flatMap natWord ++ rest := by
        rw [hip, ← List.drop_drop, hin]
        simp
      refine Hs.mono (ih hnd.2 (fun y hy => hsafe y (by simp [hy])) vs
        (by simpa using hlen) b hbc hin' (fun w hw => hW w (by simp [hw]))) le_rfl ?_
      rintro e ⟨he, heip, herest, hec, hefr⟩
      refine ⟨?_, ?_, herest.trans hrest, hec, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change e.env x = v
          rw [hefr x (by simp [hnd.1, hx.1]), hb]
        · simpa using he j
      · simp only [List.flatMap_cons, List.length_append]
        omega
      · exact Fr.trans (Fr.weaken hfr (by intro y hy; simp at hy ⊢; tauto))
          (Fr.weaken hefr (by intro y hy; simp at hy ⊢; tauto))

end NearQuarticWires.StageGamma
