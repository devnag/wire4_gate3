import Proof.Quartic.Reconstruct.EmitFinal

/-!
# Copying input bits into a record store

Paper: Step 3 of `sec:algorithm`, paper/paper.tex (each printed table receives the word after
parameter preparation and the coefficient table).

The printing stage keeps the bits of `prepWord` and of `gammaTableWord` in record stores, to write them once per
printed table. This file has the effect predicate `InMoved` (input read, records appended to one store) and the
two basic steps `rdI_spec'`, `wrM_spec'`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicWires.RepairOrdinary (frame)

variable {C : Ctx}

/-- The end flag of a frame. -/
def fE : Fin VV := ⟨84, by decide⟩
/-- The mark bit of a frame. -/
def fM : Fin VV := ⟨85, by decide⟩
/-- A data bit. -/
def fB : Fin VV := ⟨86, by decide⟩

theorem frame_nil' : frame ([] : List Bool) = [false] := rfl
theorem frame_cons' (b : Bool) (l : List Bool) : frame (b :: l) = true :: b :: frame l := rfl

theorem bitOf_drop {inp rest : List Bool} {i : ℕ} {x : Bool} (h : inp.drop i = x :: rest) :
    bitOf inp i = x.toNat ∧ i < inp.length := by
  have hl : i < inp.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    exact List.cons_ne_nil _ _ h.symm
  refine ⟨?_, hl⟩
  unfold bitOf
  rw [List.getD_eq_getElem _ _ hl]
  have := congrArg List.head? h
  rw [List.head?_drop, List.getElem?_eq_getElem hl] at this
  simp only [List.head?_cons, Option.some.injEq] at this
  rw [this]

theorem drop_succ_of_drop {inp rest : List Bool} {i : ℕ} {x : Bool} (h : inp.drop i = x :: rest) :
    inp.drop (i + 1) = rest := by
  rw [← List.drop_drop, h]; rfl

theorem putAt_end (l : List ℕ) (v : ℕ) : putAt l l.length v = l ++ [v] := by
  unfold putAt; simp

/-- The effect of reading input into store `m`: the cursor advances by `k`, the records `vs` are appended to store
`m`, the other stores and the output are unchanged, and only the variables in `T` change. -/
structure InMoved (a b : DS VV MM) (m : Fin MM) (k : ℕ) (vs : List ℕ) (T : List (Fin VV)) : Prop where
  ip : b.ip = a.ip + k
  out : b.out = a.out
  ram : b.ram m = a.ram m ++ vs
  rc : b.rc m = a.rc m + vs.length
  ramo : ∀ m', m' ≠ m → b.ram m' = a.ram m'
  rco : ∀ m', m' ≠ m → b.rc m' = a.rc m'
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  fr : Fr a b T

theorem InMoved.refl (a : DS VV MM) (m : Fin MM) (T : List (Fin VV)) : InMoved a a m 0 [] T :=
  ⟨by simp, rfl, by simp, by simp, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, Fr.refl a T⟩

theorem InMoved.trans {a b c : DS VV MM} {m : Fin MM} {k k' : ℕ} {vs vs' : List ℕ} {T : List (Fin VV)}
    (h1 : InMoved a b m k vs T) (h2 : InMoved b c m k' vs' T) : InMoved a c m (k + k') (vs ++ vs') T :=
  ⟨by rw [h2.ip, h1.ip, Nat.add_assoc], h2.out.trans h1.out, by rw [h2.ram, h1.ram, List.append_assoc],
    by rw [h2.rc, h1.rc, List.length_append, Nat.add_assoc], fun m' h => (h2.ramo m' h).trans (h1.ramo m' h),
    fun m' h => (h2.rco m' h).trans (h1.rco m' h), h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc,
    Fr.trans h1.fr h2.fr⟩

theorem InMoved.weaken {a b : DS VV MM} {m : Fin MM} {k : ℕ} {vs : List ℕ} {T T' : List (Fin VV)}
    (h : InMoved a b m k vs T) (hT : ∀ y ∈ T, y ∈ T') : InMoved a b m k vs T' :=
  ⟨h.ip, h.out, h.ram, h.rc, h.ramo, h.rco, h.kin, h.kout, h.kc, h.fr.weaken hT⟩

theorem InMoved.set {a b : DS VV MM} {m : Fin MM} {k : ℕ} {vs : List ℕ} {T : List (Fin VV)}
    (h : InMoved a b m k vs T) {x : Fin VV} (v : ℕ) (hx : x ∈ T) : InMoved a (b.set x v) m k vs T :=
  ⟨h.ip, h.out, h.ram, h.rc, h.ramo, h.rco, h.kin, h.kout, h.kc, Fr.trans h.fr (Fr.set b v hx)⟩

/-- Reading one input bit. -/
theorem rdI_spec' (y : Fin VV) (m : Fin MM) (a : DS VV MM) (x : Bool) (rest : List Bool)
    (hin : C.inp.drop a.ip = x :: rest) :
    Hs C (.op (.rdI y)) a 1 (fun b => b.env y = x.toNat ∧ C.inp.drop b.ip = rest ∧ InMoved a b m 1 [] [y]) := by
  obtain ⟨hb, hl⟩ := bitOf_drop hin
  refine Hs.mono (hs_rdI C y a hl) le_rfl ?_
  rintro b rfl
  refine ⟨by simp [DS.set, hb], drop_succ_of_drop hin, ⟨rfl, rfl, by simp [DS.set], by simp [DS.set],
    fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, ?_⟩⟩
  intro z hz
  simp only [List.mem_singleton] at hz
  simp [DS.set, Function.update_of_ne hz]

/-- Appending a record at the end of a store. -/
theorem wrM_spec' (m : Fin MM) (x : Fin VV) (a : DS VV MM) (hend : a.rc m = (a.ram m).length) :
    Hs C (.op (.wrM m x)) a 1 (fun b => InMoved a b m 0 [a.env x] [] ∧ b.env = a.env) := by
  refine Hs.mono (hs_wrM C m x a (by omega)) le_rfl ?_
  rintro b rfl
  refine ⟨⟨by simp [DS.put], by simp [DS.put], ?_, by simp [DS.put], fun m' h => by
    simp [DS.put, Function.update_of_ne h], fun m' h => by simp [DS.put, Function.update_of_ne h], by
    simp [DS.put], by simp [DS.put], by simp [DS.put], fun _ _ => rfl⟩, rfl⟩
  simp only [DS.put, Function.update_self]
  rw [hend, putAt_end]

theorem InMoved.cst {a b : DS VV MM} {m : Fin MM} {k : ℕ} {vs : List ℕ} {T : List (Fin VV)} (h : InMoved a b m k vs T)
    (hc : Cst a) (hT : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T) : Cst b := Cst.of_fr hc h.fr hT

theorem InMoved.endc {a b : DS VV MM} {m : Fin MM} {k : ℕ} {vs : List ℕ} {T : List (Fin VV)} (h : InMoved a b m k vs T)
    (hend : a.rc m = (a.ram m).length) : b.rc m = (b.ram m).length := by
  rw [h.rc, h.ram, hend, List.length_append]

end NearQuarticWires.Reconstruct
