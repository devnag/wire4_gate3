import Proof.Quartic.StageGamma.CachedSource
import Proof.Quartic.StageGamma.BinaryPower
import Proof.Wire_3_5.GF2Machines

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: one fixed
cache-bit step reads a real source bit, updates its binary value and shifts
the positional power. -/
def fixedReadBody : St VV MM :=
  .seq (.op (.rdI t0))
    (.seq (.ite (.eq t0 v1) (.op (.add t3 t1)) skipS) (.op (.shl t1)))

/-- `cor:conditional`, paper/paper.tex: the cached
low field bits are decoded with their exact ORIGINAL fixed width. -/
def fixedRead (count result : Fin VV) : St VV MM :=
  .seq (.op (.copy t4 count)) (.seq (.op (.zero t3))
    (.seq (.op (.copy t1 v1))
      (.seq (forS t2 t4 fixedReadBody) (.op (.copy result t3)))))

/-- `cor:conditional`, paper/paper.tex: the fixed
cache decoder changes only its named destination and binary scratch. -/
def fixedReadScratch (result : Fin VV) : List (Fin VV) :=
  [result, t0, t1, t2, t3, t4, vJ]

/-- `cor:conditional`, paper/paper.tex: the decoded
binary prefix grows by its actual next little-endian bit. -/
theorem mod_two_pow_next (v k : ℕ) :
    v % 2 ^ (k + 1) = v % 2 ^ k + (v.testBit k).toNat * 2 ^ k := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ k) with hm | hm <;> simp [hm] <;> ring

/-- `cor:conditional` and `prop:time`, paper/paper.tex: exact low-bit cache decoding uses O(ell) real binary
operations and preserves all ORIGINAL request fields outside scratch. -/
theorem fixedRead_run (C : Ctx) (count result : Fin VV)
    (hcount : count ∉ fixedReadScratch result)
    (hresult : result ∉ [vZ, v1, v2, t0, t1, t2, t3, t4, vJ])
    (a : DS VV MM) (hc : Cst a) (N v : ℕ) (rest : List Bool)
    (hN : a.env count = N) (hwidth : N + 1 ≤ C.Wd)
    (hin : C.inp.drop a.ip = binary N v ++ rest) :
    Hs C (fixedRead count result) a (10 * N + 18) (fun b =>
      b.env result = v % 2 ^ N ∧ b.env t1 = 2 ^ N ∧
      b.ip = a.ip + N ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (fixedReadScratch result)) := by
  have hcount4 : t4 ≠ count := by intro h; exact hcount (by simp [fixedReadScratch, h])
  have hr3 : result ≠ t3 := by intro h; exact hresult (by simp [h])
  have hconst : vZ ∉ fixedReadScratch result ∧ v1 ∉ fixedReadScratch result ∧
      v2 ∉ fixedReadScratch result := by
    simp only [fixedReadScratch, List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · constructor
      · intro h; exact hresult (by simp [h])
      · decide
    · constructor
      · constructor
        · intro h; exact hresult (by simp [h])
        · decide
      · constructor
        · intro h; exact hresult (by simp [h])
        · decide
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env t3 = v % 2 ^ k ∧ b.env t1 = 2 ^ k ∧ b.ip = a.ip + k ∧
    (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
      (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
    Fr a b (fixedReadScratch result)
  have hI : ∀ k b w, I k b → I k (b.set t2 w) := by
    intro k b w ⟨hb, hp, hi, hr, hbc, hfr⟩
    exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hb,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hp, hi, hr,
      Cst.of_fr hbc (Fr.set b w (by simp [fixedReadScratch] : t2 ∈ fixedReadScratch result)) hconst,
      hfr.trans (Fr.set b w (by simp [fixedReadScratch]))⟩
  have hbody : ∀ k < N, ∀ b, I k b → b.env t2 = k → b.env t4 = N →
      Hs C fixedReadBody b 6 (fun d => I (k + 1) d ∧ d.env t2 = k ∧ d.env t4 = N) := by
    intro k hk b ⟨hb, hp, hip, hrest, hbc, hfr⟩ hki hcn
    have hread : b.ip < C.inp.length := by
      rw [hip]
      apply lt_of_drop hin k
      simp only [SignedSortKey.binary_length]
      exact hk
    have hbit : bitOf C.inp b.ip = (v.testBit k).toNat := by
      rw [hip, bitOf_drop hin k (by simp only [SignedSortKey.binary_length]; exact hk)]
      rw [List.getD_eq_getElem _ _ (by simp only [SignedSortKey.binary_length]; exact hk),
        GF2.binary_getElem]
    have hkpow : 2 ^ (k + 1) < 2 ^ C.Wd :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    have hsum : v % 2 ^ k + 2 ^ k < 2 ^ C.Wd := by
      have hm := Nat.mod_lt v (Nat.two_pow_pos k)
      rw [pow_succ] at hkpow
      omega
    unfold fixedReadBody
    refine Hs.seq (t1 := 1) (t2 := 4) (hs_rdI C t0 b hread) ?_
    intro d hd
    subst hd
    let d : DS VV MM := { b.set t0 (bitOf C.inp b.ip) with ip := b.ip + 1 }
    have dc : Cst d := ⟨by vsimp [d, hbc.z], by vsimp [d, hbc.one], by vsimp [d, hbc.two]⟩
    have dt3 : d.env t3 = v % 2 ^ k := by vsimp [d, hb]
    have dt1 : d.env t1 = 2 ^ k := by vsimp [d, hp]
    have d0 : d.env t0 = (v.testBit k).toNat := by simp [d, hbit]
    have hstep : Hs C (.ite (.eq t0 v1) (.op (.add t3 t1)) skipS) d 2 (fun e =>
        e.env t3 = v % 2 ^ (k + 1) ∧ e.ip = d.ip ∧
        (e.out, e.ram, e.rc, e.kin, e.kout, e.kc) =
          (d.out, d.ram, d.rc, d.kin, d.kout, d.kc) ∧ Fr d e [t3, vJ]) := by
      refine Hs.ite (c := .eq t0 v1) (by change t0 ≠ v1; decide) ?_ ?_
      · intro he
        have htrue : v.testBit k = true := by
          revert he
          simp only [Cnd.eval, d0, dc.one]
          cases v.testBit k <;> simp
        refine Hs.mono (hs_add C t3 t1 d (by decide) (by rw [dt3, dt1]; exact hsum)) le_rfl ?_
        rintro e rfl
        exact ⟨by vsimp [dt3, dt1, mod_two_pow_next, htrue], rfl, rfl, Fr.set d _ (by decide)⟩
      · intro he
        have hfalse : v.testBit k = false := by
          revert he
          simp only [Cnd.eval, d0, dc.one]
          cases v.testBit k <;> simp
        refine Hs.mono (skip_spec d) le_rfl ?_
        rintro e rfl
        exact ⟨by vsimp [dt3, mod_two_pow_next, hfalse], rfl, rfl, Fr.set d _ (by decide)⟩
    refine Hs.seq (t1 := 2) (t2 := 1) hstep ?_
    intro e ⟨he, hei, herest, hefr⟩
    have et1 : e.env t1 = 2 ^ k := by rw [hefr t1 (by decide), dt1]
    have ef : Fr a e (fixedReadScratch result) :=
      hfr.trans ((Fr.set b _ (by simp [fixedReadScratch] : t0 ∈ fixedReadScratch result)).trans
        (hefr.weaken (by simp [fixedReadScratch])))
    have ec : Cst e := Cst.of_fr hc ef hconst
    refine Hs.mono (hs_shl C t1 e (by rw [et1, Nat.mul_comm 2, ← pow_succ]; exact hkpow)) le_rfl ?_
    rintro z rfl
    refine ⟨⟨by rw [DS.set_env_ne _ _ (by decide)]; exact he,
      by simp [et1, pow_succ, Nat.mul_comm], ?_, ?_,
      Cst.of_fr ec (Fr.set e _ (by simp [fixedReadScratch] : t1 ∈ fixedReadScratch result)) hconst,
      ef.trans (Fr.set e _ (by simp [fixedReadScratch]))⟩, ?_, ?_⟩
    · change e.ip = a.ip + (k + 1)
      rw [hei]
      change b.ip + 1 = a.ip + (k + 1)
      omega
    · exact herest.trans hrest
    · rw [DS.set_env_ne _ _ (by decide), hefr t2 (by decide)]
      change b.env t2 = k
      exact hki
    · rw [DS.set_env_ne _ _ (by decide), hefr t4 (by decide)]
      change b.env t4 = N
      exact hcn
  unfold fixedRead
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 10 * N + 12)
    (hs_copy C t4 count a hcount4) ?_) (by omega) (fun _ h => h)
  intro b hb
  subst hb
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 10 * N + 10) (hs_zero C t3 _) ?_)
    (by omega) (fun _ h => h)
  intro b hb
  subst hb
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 10 * N + 8)
    (hs_copy C t1 v1 _ (by decide)) ?_) (by omega) (fun _ h => h)
  intro b hb
  subst hb
  let b := ((a.set t4 (a.env count)).set t3 0).set t1
    (((a.set t4 (a.env count)).set t3 0).env v1)
  have hf : Fr a b (fixedReadScratch result) :=
    (Fr.set a _ (by simp [fixedReadScratch])).trans
      ((Fr.set _ _ (by simp [fixedReadScratch])).trans (Fr.set _ _ (by simp [fixedReadScratch])))
  have hb0 : I 0 b := ⟨by vsimp [b, Nat.mod_one], by vsimp [b, hc.one],
    by simp [b], rfl, Cst.of_fr hc hf hconst, hf⟩
  have hnfit : N < 2 ^ C.Wd := by
    have h : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
    omega
  refine Hs.mono (Hs.seq (t1 := N * 10 + 4) (t2 := 1)
    (forS_spec' t2 t4 (by decide) fixedReadBody b N hnfit I 6 hI hb0
      (by vsimp [b, hN]) hbody) ?_) (by omega) (fun _ h => h)
  intro e ⟨⟨he, hp, hip, hrest, hec, hefr⟩, _, _⟩
  refine Hs.mono (hs_copy C result t3 e hr3) le_rfl ?_
  rintro z rfl
  have hrt1 : t1 ≠ result := by intro h; exact hresult (by simp [← h])
  exact ⟨by simp [he], by rw [DS.set_env_ne _ _ hrt1]; exact hp, hip, hrest,
    Cst.of_fr hec (Fr.set e _ (by simp [fixedReadScratch] : result ∈ fixedReadScratch result)) hconst,
    hefr.trans (Fr.set e _ (by simp [fixedReadScratch]))⟩

end NearQuarticWires.StageGamma
