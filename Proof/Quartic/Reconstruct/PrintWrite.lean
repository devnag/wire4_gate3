import Proof.Quartic.Reconstruct.PrintEnum

/-!
# Writing from variables and record stores

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

The printing stage writes numbers held in variables (`emitV`) and the records of a store (`emitStoreS`), at a depth
`d` of marks. `OutMoved` is the effect of such writers: the output grows, the input and the stores are unchanged, the
store cursors may move but stay in range.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

/-- The effect of a writer: `w` is written, the input and the stores are unchanged, the cursors stay in range, and
only the variables in `T` change. -/
structure OutMoved (a b : DS VV MM) (w : List Bool) (T : List (Fin VV)) : Prop where
  out : b.out = a.out ++ w
  ip : b.ip = a.ip
  ram : b.ram = a.ram
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  fr : Fr a b T
  rcok : ∀ m, b.rc m ≤ (b.ram m).length

theorem OutMoved.trans {a b c : DS VV MM} {w w' : List Bool} {T : List (Fin VV)} (h1 : OutMoved a b w T)
    (h2 : OutMoved b c w' T) : OutMoved a c (w ++ w') T :=
  ⟨by rw [h2.out, h1.out, List.append_assoc], h2.ip.trans h1.ip, h2.ram.trans h1.ram, h2.kin.trans h1.kin,
    h2.kout.trans h1.kout, h2.kc.trans h1.kc, Fr.trans h1.fr h2.fr, h2.rcok⟩

theorem OutMoved.weaken {a b : DS VV MM} {w : List Bool} {T T' : List (Fin VV)} (h : OutMoved a b w T)
    (hT : ∀ y ∈ T, y ∈ T') : OutMoved a b w T' :=
  ⟨h.out, h.ip, h.ram, h.kin, h.kout, h.kc, h.fr.weaken hT, h.rcok⟩

theorem OutMoved.set {a b : DS VV MM} {w : List Bool} {T : List (Fin VV)} (h : OutMoved a b w T) {x : Fin VV}
    (v : ℕ) (hx : x ∈ T) : OutMoved a (b.set x v) w T :=
  ⟨h.out, h.ip, h.ram, h.kin, h.kout, h.kc, Fr.trans h.fr (Fr.set b v hx), h.rcok⟩

theorem OutMoved.of_wrote {a b : DS VV MM} {w : List Bool} {T : List (Fin VV)} (h : Wrote a b w T)
    (hok : ∀ m, a.rc m ≤ (a.ram m).length) : OutMoved a b w T :=
  ⟨h.out, h.ip, h.ram, h.kin, h.kout, h.kc, h.fr, fun m => by rw [h.rc, h.ram]; exact hok m⟩

theorem OutMoved.refl (a : DS VV MM) (T : List (Fin VV)) (hok : ∀ m, a.rc m ≤ (a.ram m).length) :
    OutMoved a a [] T := ⟨by simp, rfl, rfl, rfl, rfl, rfl, Fr.refl a T, hok⟩

theorem OutMoved.cst {a b : DS VV MM} {w : List Bool} {T : List (Fin VV)} (h : OutMoved a b w T) (hc : Cst a)
    (hT : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T) : Cst b := Cst.of_fr hc h.fr hT

/-- Rewinding a store. -/
theorem rwM_spec' (m : Fin MM) (a : DS VV MM) (hok : ∀ m, a.rc m ≤ (a.ram m).length) (T : List (Fin VV)) :
    Hs C (.op (.rwM m)) a (a.rc m + 1) (fun b => OutMoved a b [] T ∧ b.rc m = 0 ∧ b.env = a.env) := by
  refine Hs.mono (hs_rwM C m a) le_rfl ?_
  rintro b rfl
  refine ⟨⟨by simp [DS.rew], rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun m' => ?_⟩, by simp [DS.rew], rfl⟩
  by_cases h : m' = m
  · subst h; simp [DS.rew]
  · simp only [DS.rew, Function.update_of_ne h]; exact hok m'

/-- Reading the next record of a store. -/
theorem rdM_spec' (m : Fin MM) (x : Fin VV) (a : DS VV MM) (h : a.rc m < (a.ram m).length)
    (hok : ∀ m, a.rc m ≤ (a.ram m).length) :
    Hs C (.op (.rdM m x)) a 1 (fun b => b.env x = (a.ram m).getD (a.rc m) 0 ∧ b.rc m = a.rc m + 1 ∧
      OutMoved a b [] [x]) := by
  refine Hs.mono (hs_rdM C m x a h) le_rfl ?_
  rintro b rfl
  refine ⟨by simp [DS.adv], by simp [DS.adv], ⟨by simp [DS.adv], by simp [DS.adv], by simp [DS.adv], by simp [DS.adv],
    by simp [DS.adv], by simp [DS.adv], fun y hy => ?_, fun m' => ?_⟩⟩
  · simp only [List.mem_singleton] at hy; simp [DS.adv, DS.set, Function.update_of_ne hy]
  · by_cases hm : m' = m
    · subst hm; simp [DS.adv]; omega
    · simp only [DS.adv, DS.set, Function.update_of_ne hm]; exact hok m'

/-- Write the number held in `x` at depth `d`. -/
def emitV (x : Fin VV) (d : ℕ) : St VV MM := .seq (.op (.copy t3 x)) (emitNatD d)

/-- The variables written by `emitV`. -/
def emitVT : List (Fin VV) := t3 :: emitNatDT

theorem emitV_spec (x : Fin VV) (hx : x ≠ t3) (d : ℕ) (a : DS VV MM) (hc : Cst a)
    (hok : ∀ m, a.rc m ≤ (a.ram m).length) (hW : 2 ≤ C.Wd) (hv : natBitLength (a.env x) + 2 < 2 ^ C.Wd) :
    Hs C (emitV x d) a (emitNatDCost d (natBitLength (a.env x)) + 2)
      (fun b => OutMoved a b (marksD d (natWord (a.env x))) emitVT ∧ Cst b) := by
  refine Hx.hs (Hs.then (hs_copy C t3 x a (Ne.symm hx)) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have c0 : Cst (a.set t3 (a.env x)) := ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩
  refine Hs.last (emitNatD_spec d _ c0 hW (by rw [DS.set_env_self]; exact hv)) (fun b ⟨w1, c1⟩ n hn => ⟨⟨?_, c1⟩, ?_⟩)
  · rw [DS.set_env_self] at w1
    exact ⟨by rw [w1.out, DS.set_out], by rw [w1.ip, DS.set_ip], by rw [w1.ram, DS.set_ram],
      by rw [w1.kin, DS.set_kin], by rw [w1.kout, DS.set_kout], by rw [w1.kc, DS.set_kc],
      Fr.trans (Fr.set a _ List.mem_cons_self) (w1.fr.weaken (fun y hy => List.mem_cons_of_mem _ hy)),
      fun m => by rw [w1.rc, w1.ram, DS.set_rc, DS.set_ram]; exact hok m⟩
  · rw [DS.set_env_self] at hn; omega

/-- Write the records of store `m`, one per run of `em` (which writes from `t3`), for `i = 0, …, n - 1`. -/
def emitStoreS (m : Fin MM) (i n : Fin VV) (em : St VV MM) : St VV MM :=
  .seq (.op (.rwM m)) (forS i n (.seq (.op (.rdM m t3)) em))

theorem getD_range_flatMap {α : Type} (vs : List ℕ) (f : ℕ → List α) :
    (List.range vs.length).flatMap (fun k => f (vs.getD k 0)) = vs.flatMap f := by
  have : (List.range vs.length).map (fun k => vs.getD k 0) = vs := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp [List.getElem?_eq_getElem (by simpa using h1)]
  conv_rhs => rw [← this]
  rw [List.flatMap_map]

/-- **Writing the records of a store.** -/
theorem emitStoreS_spec (m : Fin MM) (i n : Fin VV) (em : St VV MM) (wf : ℕ → List Bool) (Tem : List (Fin VV))
    (te : ℕ) (hi : i ∉ Tem ∧ n ∉ Tem ∧ i ≠ n ∧ i ≠ t3 ∧ n ≠ t3) (hT : vZ ∉ Tem ∧ v1 ∉ Tem ∧ v2 ∉ Tem)
    (hiC : vZ ≠ i ∧ v1 ≠ i ∧ v2 ≠ i)
    (vs : List ℕ) (hem : ∀ a : DS VV MM, Cst a → (∀ m, a.rc m ≤ (a.ram m).length) → a.env t3 ∈ vs →
      Hs C em a te (fun b => OutMoved a b (wf (a.env t3)) Tem ∧ b.rc = a.rc ∧ Cst b))
    (a : DS VV MM) (hc : Cst a) (hok : ∀ m, a.rc m ≤ (a.ram m).length) (hm : a.ram m = vs)
    (hn : a.env n = vs.length) (hN : vs.length < 2 ^ C.Wd) :
    Hs C (emitStoreS m i n em) a (a.rc m + 1 + (vs.length * (te + 1 + 1 + 4) + 4) + 1)
      (fun b => OutMoved a b (vs.flatMap wf) (i :: t3 :: Tem) ∧ Cst b) := by
  set T := i :: t3 :: Tem with hTd
  have hT' : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hTd, List.mem_cons, not_or]
    · exact ⟨hiC.1, by decide, hT.1⟩
    · exact ⟨hiC.2.1, by decide, hT.2.1⟩
    · exact ⟨hiC.2.2, by decide, hT.2.2⟩
  refine Hx.hs (Hs.then (rwM_spec' m a hok T) (fun b0 ⟨o0, r0, e0⟩ n0 hn0 => ?_))
  have c0 : Cst b0 := ⟨by rw [e0]; exact hc.z, by rw [e0]; exact hc.one, by rw [e0]; exact hc.two⟩
  let Inv : ℕ → DS VV MM → Prop := fun k b => Cst b ∧ b.rc m = k ∧ b.ram = a.ram ∧ b.ip = a.ip ∧ b.kin = a.kin ∧
    b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b T ∧ (∀ m, b.rc m ≤ (b.ram m).length)
  have hset : ∀ k b v, Inv k b → Inv k (b.set i v) := fun k b v ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ =>
    ⟨Cst.of_fr h1 (Fr.set b v (List.mem_singleton_self i)) (by
      simp only [List.mem_singleton]
      exact ⟨fun h => hT'.1 (h ▸ List.mem_cons_self), fun h => hT'.2.1 (h ▸ List.mem_cons_self),
        fun h => hT'.2.2 (h ▸ List.mem_cons_self)⟩), h2, h3, h4, h5, h6, h7, Fr.trans h8 (Fr.set b v List.mem_cons_self), h9⟩
  refine Hs.last (forS_spec i n hi.2.2.1 _ vs.length (te + 1 + 1) (fun k => wf (vs.getD k 0)) Inv hset ?_ b0
    ⟨c0, r0, o0.ram, o0.ip, o0.kin, o0.kout, o0.kc, o0.fr, o0.rcok⟩ (by rw [e0]; exact hn) hN)
    (fun b ⟨⟨b1, _, b3, b4, b5, b6, b7, b8, b9⟩, _, b10⟩ k hk => ⟨⟨⟨?_, b4, b3, b5, b6, b7, b8, b9⟩, b1⟩, by omega⟩)
  · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ hik hnk
    have hlt : b.rc m < (b.ram m).length := by rw [h2, h3, hm]; exact hk
    refine (Hs.seq (t1 := 1) (t2 := te) (rdM_spec' m t3 b hlt h9) (fun c ⟨x1, x2, x3⟩ => ?_)).mono (by omega)
      (fun _ h => h)
    have cc : Cst c := x3.cst h1 (by decide)
    have hmem : c.env t3 ∈ vs := by
      rw [x1, h2, h3, hm, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    refine Hs.mono (hem c cc x3.rcok hmem) le_rfl (fun e ⟨y1, y2, y3⟩ => ⟨⟨y3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, y1.rcok⟩, ?_, ?_, ?_⟩)
    · rw [y2, x2, h2]
    · rw [y1.ram, x3.ram, h3]
    · rw [y1.ip, x3.ip, h4]
    · rw [y1.kin, x3.kin, h5]
    · rw [y1.kout, x3.kout, h6]
    · rw [y1.kc, x3.kc, h7]
    · exact Fr.trans h8 (Fr.trans (x3.fr.weaken (fun y hy => by
        simp only [List.mem_singleton] at hy; rw [hy, hTd]; exact List.mem_cons_of_mem _ List.mem_cons_self))
        (y1.fr.weaken (fun y hy => by rw [hTd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))))
    · rw [y1.fr i hi.1, x3.fr i (by simpa using hi.2.2.2.1), hik]
    · rw [y1.fr n hi.2.1, x3.fr n (by simpa using hi.2.2.2.2), hnk]
    · rw [y1.out, x3.out, List.append_nil, x1, h2, h3, hm]
  · rw [b10, o0.out, List.append_nil, getD_range_flatMap]

end NearQuarticWires.Reconstruct
