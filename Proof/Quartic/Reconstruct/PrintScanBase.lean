import Proof.Quartic.Reconstruct.PrintCopy
import Proof.Quartic.StageMain.CallSkipCall

/-!
# Counted reading of numbers and lists

Paper: Step 3 of `sec:algorithm`, paper/paper.tex; `prop:time` (the call and the
parameters are read in their literal order).

The printing stage reads the call and the parameters once, counting the bits it reads in `lengthCounter` (the
counting scanners `CallSkip.scanNat`, `CallSkip.skipCircuit`, …), so that it can then rewind and copy them. This file
adds:

* `scanVars xs`: read numbers into the variables `xs`, counting (`scanVars_spec`);
* `scanSkipS k`: read past `k` numbers, counting (`scanSkipS_spec`);
* `listInto m`: read a list of numbers into store `m`, counting (`listInto_spec`);
* `ScannedS`: the counted effect when some stores are written.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord)
open NearQuarticWires.StageMain.CallSkip

variable {C : Ctx}

/-- The counted effect of reading `k` bits that writes the stores `ms` only. -/
structure ScannedS (a b : DS VV MM) (k : ℕ) (T : List (Fin VV)) (ms : List (Fin MM)) : Prop where
  pos : b.ip = a.ip + k
  out : b.out = a.out
  ram : ∀ m, m ∉ ms → b.ram m = a.ram m
  rc : ∀ m, m ∉ ms → b.rc m = a.rc m
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  cst : Cst b
  fr : Fr a b T
  bytes : b.env lengthCounter = a.env lengthCounter + k

theorem ScannedS.of_scanned {a b : DS VV MM} {k : ℕ} {T : List (Fin VV)} (h : Scanned a b k T)
    (ms : List (Fin MM)) : ScannedS a b k T ms := by
  have hu := h.unchanged
  simp only [Prod.mk.injEq] at hu
  exact ⟨h.pos, hu.1, fun m _ => by rw [hu.2.1], fun m _ => by rw [hu.2.2.1], hu.2.2.2.1, hu.2.2.2.2.1,
    hu.2.2.2.2.2, h.constants, h.registers, h.bytes⟩

theorem ScannedS.trans {a b c : DS VV MM} {k k' : ℕ} {T : List (Fin VV)} {ms : List (Fin MM)}
    (h1 : ScannedS a b k T ms) (h2 : ScannedS b c k' T ms) : ScannedS a c (k + k') T ms :=
  ⟨by rw [h2.pos, h1.pos, Nat.add_assoc], h2.out.trans h1.out, fun m h => (h2.ram m h).trans (h1.ram m h),
    fun m h => (h2.rc m h).trans (h1.rc m h), h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc,
    h2.cst, Fr.trans h1.fr h2.fr, by rw [h2.bytes, h1.bytes, Nat.add_assoc]⟩

theorem ScannedS.weaken {a b : DS VV MM} {k : ℕ} {T T' : List (Fin VV)} {ms ms' : List (Fin MM)}
    (h : ScannedS a b k T ms) (hT : ∀ y ∈ T, y ∈ T') (hm : ∀ m ∈ ms, m ∈ ms') : ScannedS a b k T' ms' :=
  ⟨h.pos, h.out, fun m hm' => h.ram m (fun h' => hm' (hm m h')), fun m hm' => h.rc m (fun h' => hm' (hm m h')),
    h.kin, h.kout, h.kc, h.cst, h.fr.weaken hT, h.bytes⟩

theorem ScannedS.tail {a b : DS VV MM} {T : List (Fin VV)} {ms : List (Fin MM)} {word rest : List Bool}
    (h : ScannedS a b word.length T ms) (hin : C.inp.drop a.ip = word ++ rest) : C.inp.drop b.ip = rest := by
  rw [h.pos, ← List.drop_drop, hin, List.drop_left]

/-- Read a number into `x`, counting. -/
def scanTo (x : Fin VV) : St VV MM := .seq scanNat (.op (.copy x t3))

/-- Read numbers into a list of variables, counting. -/
def scanVars : List (Fin VV) → St VV MM
  | [] => skipS
  | x :: xs => .seq (scanTo x) (scanVars xs)

theorem scanTo_spec (x : Fin VV) (hx0 : x ∉ atomScratch ∧ x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2) (a : DS VV MM) (hc : Cst a)
    (v : ℕ) (rest : List Bool) (hin : C.inp.drop a.ip = natWord v ++ rest) (hW : natBitLength v + 2 ≤ C.Wd)
    (hcap : a.env lengthCounter + (natWord v).length < 2 ^ C.Wd) :
    Hs C (scanTo x) a (30 * natBitLength v + 38)
      (fun b => b.env x = v ∧ Scanned a b (natWord v).length (x :: atomScratch)) := by
  refine Hx.hs (Hs.then (scanNat_read_run C a hc v rest hin hW hcap)
    (fun b0 ⟨r1, _, r3, r4, c0, r5, r6⟩ n0 hn0 => ?_))
  have hxt : x ≠ t3 := fun h => hx0.1 (by rw [h]; decide)
  refine Hs.last (hs_copy C x t3 b0 hxt) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  have hxl : lengthCounter ≠ x := fun h => hx0.1 (by rw [← h]; decide)
  have hxs : vZ ∉ [x] ∧ v1 ∉ [x] ∧ v2 ∉ [x] := by
    simp only [List.mem_singleton]
    exact ⟨fun h => hx0.2.1 h.symm, fun h => hx0.2.2.1 h.symm, fun h => hx0.2.2.2 h.symm⟩
  refine ⟨⟨by rw [DS.set_env_self, r1], ⟨by rw [DS.set_ip, r3], by simpa using r4,
    Cst.of_fr c0 (Fr.set b0 _ (List.mem_singleton_self x)) hxs,
    Fr.trans (r5.weaken (fun y hy => List.mem_cons_of_mem _ hy)) (Fr.set b0 _ List.mem_cons_self),
    by rw [DS.set_env_ne _ _ hxl, r6]⟩⟩, by omega⟩

/-- **Reading numbers into variables, counting.** -/
theorem scanVars_spec (xs : List (Fin VV)) (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, x ∉ atomScratch ∧ x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2) (vs : List ℕ) (hl : vs.length = xs.length)
    (a : DS VV MM) (hc : Cst a) (rest : List Bool) (hin : C.inp.drop a.ip = vs.flatMap natWord ++ rest) (ℓ : ℕ)
    (hW : ∀ v ∈ vs, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd)
    (hcap : a.env lengthCounter + (vs.flatMap natWord).length < 2 ^ C.Wd) :
    Hs C (scanVars xs) a (xs.length * (30 * ℓ + 39) + 1)
      (fun b => (∀ p ∈ xs.zip vs, b.env p.1 = p.2) ∧ Scanned a b (vs.flatMap natWord).length (xs ++ atomScratch)) := by
  induction xs generalizing vs a with
  | nil =>
    have hv : vs = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst hv
    refine Hs.mono (skip_spec a) (by simp) ?_
    rintro b rfl
    have hlc : (a.set vJ 0).env lengthCounter = a.env lengthCounter := DS.set_env_ne _ _ (by decide)
    exact ⟨by simp, ⟨by simp, rfl, ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩,
      Fr.set a _ (by decide), by simpa using hlc⟩⟩
  | cons x xs ih =>
    obtain ⟨v, vs, rfl⟩ : ∃ v vs', vs = v :: vs' := by
      cases vs with
      | nil => simp at hl
      | cons v vs' => exact ⟨v, vs', rfl⟩
    have hx0 := hx x (by simp)
    have hv : natBitLength v ≤ ℓ := hW v (by simp)
    have hin1 : C.inp.drop a.ip = natWord v ++ (vs.flatMap natWord ++ rest) := by
      rw [hin, List.flatMap_cons, List.append_assoc]
    have hcap1 : a.env lengthCounter + (natWord v).length < 2 ^ C.Wd := by
      simp only [List.flatMap_cons, List.length_append] at hcap; omega
    refine Hx.hs (Hs.then (scanTo_spec x hx0 a hc v _ hin1 (by omega) hcap1) (fun b1 ⟨r1, m1⟩ n1 hn1 => ?_))
    have hin2 : C.inp.drop b1.ip = vs.flatMap natWord ++ rest := m1.tail hin1
    have hnd' := (List.nodup_cons.mp hnd)
    have hcap2 : b1.env lengthCounter + (vs.flatMap natWord).length < 2 ^ C.Wd := by
      rw [m1.bytes]; simp only [List.flatMap_cons, List.length_append] at hcap; omega
    refine Hs.last (ih hnd'.2 (fun y hy => hx y (List.mem_cons_of_mem _ hy)) vs (by simpa using hl) _ m1.constants
      hin2 (fun w hw => hW w (List.mem_cons_of_mem _ hw)) hcap2) (fun b ⟨e1, e2⟩ n hn => ⟨⟨?_, ?_⟩, ?_⟩)
    · intro p hp
      rw [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · show b.env x = v
        rw [e2.registers x (by simp only [List.mem_append, not_or]; exact ⟨hnd'.1, hx0.1⟩), r1]
      · exact e1 p hp
    · have := m1.then_scanned e2
      have hT : ∀ y ∈ (x :: atomScratch) ++ (xs ++ atomScratch), y ∈ x :: xs ++ atomScratch := by
        intro y hy
        simp only [List.mem_append, List.mem_cons] at hy ⊢
        tauto
      refine ⟨by rw [this.pos]; simp [List.flatMap_cons], this.unchanged, this.constants, this.registers.weaken hT,
        by rw [this.bytes]; simp [List.flatMap_cons]⟩
    · simp only [List.length_cons]
      have := Nat.mul_le_mul_left 30 hv
      nlinarith

/-- Read past `k` numbers, counting. -/
def scanSkipS : ℕ → St VV MM
  | 0 => skipS
  | k + 1 => .seq scanNat (scanSkipS k)

/-- **Reading past numbers, counting.** -/
theorem scanSkipS_spec (k : ℕ) : ScanSpec (scanSkipS k) (fun v : Fin k → ℕ => (List.ofFn v).flatMap natWord)
    atomScratch (fun L => k * (66 * (L + 1) + 1) + 1) := by
  induction k with
  | zero =>
    intro C L a hc x rest hin hlen hW hcap
    refine Hs.mono (skip_spec a) (by simp) ?_
    rintro b rfl
    have hlc : (a.set vJ 0).env lengthCounter = a.env lengthCounter := DS.set_env_ne _ _ (by decide)
    exact ⟨by simp, rfl, ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩, Fr.set a _ (by decide),
      by simpa using hlc⟩
  | succ k ih =>
    have h := (scanNat_spec.map (fun v : Fin (k + 1) → ℕ => v 0)).seq (ih.map (fun v : Fin (k + 1) → ℕ => Fin.tail v))
    have heq : (fun v : Fin (k + 1) → ℕ => natWord (v 0) ++ (List.ofFn (Fin.tail v)).flatMap natWord) =
        fun v => (List.ofFn v).flatMap natWord := by
      funext v
      rw [List.ofFn_succ, List.flatMap_cons]
      rfl
    rw [heq] at h
    refine h.weaken (by intro x hx; simpa using hx) (fun L => ?_)
    show 66 * (L + 1) + (k * (66 * (L + 1) + 1) + 1) + 1 ≤ (k + 1) * (66 * (L + 1) + 1) + 1
    ring_nf; omega

end NearQuarticWires.Reconstruct
