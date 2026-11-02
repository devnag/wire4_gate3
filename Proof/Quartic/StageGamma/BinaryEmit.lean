import Proof.Quartic.StageGamma.Emit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTablesProg

/-- `cor:conditional`, paper/paper.tex: emit the fixed
record code selected by one computed bit. -/
def emitCode (x : Fin VV) (code : Bool → List Bool) : St VV MM :=
  .ite (.eq x v1) (emitBits (code true)) (emitBits (code false))

/-- `cor:conditional`, paper/paper.tex: a computed
bit controls real marker emission, preserving every other source field. -/
theorem emitCode_spec (C : Ctx) (x : Fin VV) (hx : x ≠ v1)
    (code : Bool → List Bool) (D : ℕ) (hD : ∀ bit, (code bit).length ≤ D)
    (a : DS VV MM) (hc : Cst a) (hroom : a.kin.length + D ≤ C.Lk) :
    Hs C (emitCode x code) a (2 * D + 2) (fun b =>
      b.kin = a.kin ++ code (decide (a.env x = 1)) ∧
      SameN a b ∧ Cst b ∧ Fr a b [vJ]) := by
  refine Hs.ite (c := .eq x v1) (t := 2 * D + 1) hx ?_ ?_
  · intro ht
    have hv : a.env x = 1 := by simpa [Cnd.eval, hc.one] using ht
    refine Hs.mono (emitBits_spec C (code true) a hc (by have := hD true; omega))
      (by have := hD true; omega) ?_
    intro b hb
    simpa [hv] using hb
  · intro ht
    have hv : a.env x ≠ 1 := by simpa [Cnd.eval, hc.one] using ht
    refine Hs.mono (emitBits_spec C (code false) a hc (by have := hD false; omega))
      (by have := hD false; omega) ?_
    intro b hb
    simpa [hv] using hb

/-- `prop:time`, paper/paper.tex: coded payload
length is bounded by the actual number of source bits. -/
theorem coded_length_le (code : Bool → List Bool) (D : ℕ)
    (hD : ∀ bit, (code bit).length ≤ D) (bits : List Bool) :
    (bits.flatMap code).length ≤ bits.length * D := by
  induction bits with
  | nil => simp
  | cons bit bits ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hh := hD bit
    nlinarith

/-- `cor:conditional`, paper/paper.tex: fixed binary
payload scratch variables, separate from every original request field. -/
def binaryIndex : Fin VV := ⟨54, by decide⟩
def binaryWork : Fin VV := ⟨55, by decide⟩
def binaryQuot : Fin VV := ⟨56, by decide⟩
def binaryRem : Fin VV := ⟨57, by decide⟩

/-- `cor:conditional`, paper/paper.tex: only these
scratch variables may change during binary payload emission. -/
def binaryScratch : List (Fin VV) := [binaryIndex, binaryWork, binaryQuot, binaryRem, vJ]

/-- `cor:conditional`, paper/paper.tex: one payload
iteration preserves its loop index as well as every source field. -/
def binaryBodyScratch : List (Fin VV) := [binaryWork, binaryQuot, binaryRem, vJ]

/-- `cor:conditional`, paper/paper.tex: one real
division by two emits the selected low bit's marker code. -/
def binaryEmitBody (code : Bool → List Bool) : St VV MM :=
  .seq (.op (.dm binaryWork v2 binaryQuot binaryRem))
    (.seq (.op (.copy binaryWork binaryQuot)) (emitCode binaryRem code))

/-- `cor:conditional`, paper/paper.tex: emit precisely
the requested number of low binary digits, including leading zero bits. -/
def binaryEmit (count value : Fin VV) (code : Bool → List Bool) : St VV MM :=
  .seq (.op (.copy binaryWork value)) (forS binaryIndex count (binaryEmitBody code))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: every fixed-width payload bit is physically computed and
written with linear source-language work. -/
theorem binaryEmit_spec (C : Ctx) (count value : Fin VV)
    (hcount : count ∉ binaryScratch) (hvalue : value ∉ binaryScratch)
    (code : Bool → List Bool) (D : ℕ) (hD : ∀ bit, (code bit).length ≤ D)
    (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd)
    (N v : ℕ) (hN : a.env count = N) (hv : a.env value = v)
    (hNW : N < 2 ^ C.Wd) (hroom : a.kin.length + N * D ≤ C.Lk) :
    Hs C (binaryEmit count value code) a (N * (2 * D + 10) + 6) (fun b =>
      b.kin = a.kin ++ ((List.range N).map v.testBit).flatMap code ∧
      SameN a b ∧ Cst b ∧ Fr a b binaryScratch) := by
  have hcI : binaryIndex ≠ count := by intro h; exact hcount (by simp [binaryScratch, ← h])
  have hvW : binaryWork ≠ value := by intro h; exact hvalue (by simp [binaryScratch, ← h])
  unfold binaryEmit
  refine Hs.mono (Hs.seq (t2 := N * (2 * D + 10) + 4)
    (hs_copy C binaryWork value a hvW) (fun a1 ha1 => ?_)) (by omega) (fun _ h => h)
  subst ha1
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env binaryWork = v / 2 ^ k ∧
    b.kin = a.kin ++ ((List.range k).map v.testBit).flatMap code ∧
    SameN a b ∧ Cst b ∧ Fr a b binaryScratch
  have hIi : ∀ k b w, I k b → I k (b.set binaryIndex w) := by
    intro k b w ⟨hw, hk, hs, hbc, hfr⟩
    exact ⟨by rw [DS.set_env_ne _ _ (show binaryWork ≠ binaryIndex by decide)]; exact hw, hk,
      hs.trans (SameN.set _ _ _),
      Cst.of_fr (T := [binaryIndex]) hbc (Fr.set b w (by simp)) (by decide),
      hfr.trans (Fr.set b w (by simp [binaryScratch]))⟩
  have h0 : I 0 (a.set binaryWork (a.env value)) := by
    refine ⟨by simp [hv], by simp, SameN.set _ _ _, ?_, Fr.set a _ (by simp [binaryScratch])⟩
    exact Cst.of_fr (T := [binaryWork]) hc (Fr.set a _ (by simp)) (by decide)
  refine Hs.mono (forS_spec' binaryIndex count hcI (binaryEmitBody code)
    (a.set binaryWork (a.env value)) N hNW I (2 * D + 6) hIi h0
    (by rw [DS.set_env_ne _ _ (by intro heq; exact hcount (by simp [binaryScratch, heq]))]; exact hN) ?_)
    (by nlinarith) ?_
  · intro k hk b ⟨hw, hb, hs, hbc, hfr⟩ hki hcn
    have hdm := hs_dm C binaryWork v2 binaryQuot binaryRem b (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by rw [hbc.two]; decide)
      (by rw [hbc.two]; exact Nat.pow_le_pow_right (n := 2) (by decide) hW)
    refine Hs.mono (Hs.seq (t2 := 2 * D + 4) hdm (fun b1 hb1 => ?_))
      (by omega) (fun _ h => h)
    subst hb1
    refine Hs.mono (Hs.seq (t2 := 2 * D + 2)
      (hs_copy C binaryWork binaryQuot _ (by decide)) (fun b2 hb2 => ?_))
      (by omega) (fun _ h => h)
    subst hb2
    let b2 := ((b.set binaryQuot (b.env binaryWork / b.env v2)).set binaryRem
      (b.env binaryWork % b.env v2)).set binaryWork (b.env binaryWork / b.env v2)
    have hf2 : Fr b b2 binaryBodyScratch :=
      (Fr.set b _ (by simp [binaryBodyScratch])).trans
        ((Fr.set _ _ (by simp [binaryBodyScratch])).trans (Fr.set _ _ (by simp [binaryBodyScratch])))
    have hs2 : SameN b b2 :=
      (SameN.set _ _ _).trans ((SameN.set _ _ _).trans (SameN.set _ _ _))
    have hc2 : Cst b2 := Cst.of_fr hbc hf2 (by decide)
    have hbit : decide (b2.env binaryRem = 1) = v.testBit k := by
      vsimp [b2, hw, hbc.two, Nat.testBit_eq_decide_div_mod_eq]
    have hroom2 : b2.kin.length + D ≤ C.Lk := by
      change b.kin.length + D ≤ C.Lk
      rw [hb, List.length_append]
      have hl := coded_length_le code D hD ((List.range k).map v.testBit)
      simp only [List.length_map, List.length_range] at hl
      have hm := Nat.mul_le_mul_right D (show k + 1 ≤ N by omega)
      nlinarith
    refine Hs.mono (emitCode_spec C binaryRem (by decide) code D hD b2 hc2 hroom2) le_rfl ?_
    rintro e ⟨he, hes, hec, hefr⟩
    have hef : Fr b e binaryBodyScratch := hf2.trans (hefr.weaken (by simp [binaryBodyScratch]))
    refine ⟨⟨?_, ?_, hs.trans (hs2.trans hes), hec,
      hfr.trans (hef.weaken (by simp [binaryBodyScratch, binaryScratch]))⟩, ?_, ?_⟩
    · rw [hefr binaryWork (by decide)]
      change b.env binaryWork / b.env v2 = _
      rw [hw, hbc.two, Nat.div_div_eq_div_mul, pow_succ]
    · rw [he, hbit]
      change b.kin ++ code (v.testBit k) = _
      rw [hb, List.range_succ, List.map_append, List.flatMap_append]
      simp [List.append_assoc]
    · rw [hef binaryIndex (by decide)]
      exact hki
    · rw [hef count (by
        intro hh
        apply hcount
        simp only [binaryBodyScratch, binaryScratch, List.mem_cons, List.not_mem_nil, or_false] at *
        tauto)]
      exact hcn
  · rintro b ⟨⟨_, hb, hs, hbc, hfr⟩, _, _⟩
    exact ⟨hb, hs, hbc, hfr⟩

end NearQuarticWires.StageGamma
