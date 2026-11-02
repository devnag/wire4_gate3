import Proof.Quartic.StageRecovery.FixedField

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery.FixedBits

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: a literal source
register is copied into the binary writer before its field is emitted. -/
def emitFieldFrom (x : Fin VV) : St VV MM :=
  .seq (.op (.copy value x)) emitFixedField

/-- `lem:print`, paper/paper.tex: every fixed-width
field is emitted from its actual runtime register, with both framing
layers and copying paid in the source clock. -/
theorem emitFieldFrom_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (x : Fin VV) (hx : x ∉ fieldScratch) (W : ℕ) (hw : a.env width = W)
    (hW : W < 2 ^ C.Wd) (hctx : 2 ≤ C.Wd) :
    Hs C (emitFieldFrom x) a (18 * W + 14) (fun b =>
      b.out = a.out ++ frame (frame (binary W (a.env x))) ∧
      outputRest b = outputRest a ∧ b.env width = W ∧ Cst b ∧ Fr a b fieldScratch) := by
  have hxv : value ≠ x := by
    intro he
    apply hx
    rw [← he]
    decide
  unfold emitFieldFrom
  refine (Hs.seq (t2 := 18 * W + 12) (hs_copy C value x a hxv) fun b hb => ?_).mono
    (by omega) (fun _ h => h)
  subst b
  have hf : Fr a (a.set value (a.env x)) fieldScratch := Fr.set _ _ (by decide)
  refine (emitFixedField_spec C _ (Cst.of_fr hc hf (by decide)) (a.env x) W rfl
    (by simpa (config := {decide := true}) [DS.set] using hw) hW hctx).mono le_rfl ?_
  rintro b ⟨h1, h2, h3, h4, h5⟩
  exact ⟨h1, h2, h3, h4, Fr.trans hf h5⟩

/-- `lem:print`, paper/paper.tex: a fixed finite list
of source registers is serialized without a supplied output record. -/
def emitFields : List (Fin VV) → St VV MM
  | [] => skipS
  | x :: xs => .seq (emitFieldFrom x) (emitFields xs)

/-- `lem:print`, paper/paper.tex: the complete scalar
field block preserves all source registers outside its five writer words. -/
theorem emitFields_spec (C : Ctx) (xs : List (Fin VV)) (a : DS VV MM) (hc : Cst a)
    (hxs : ∀ x ∈ xs, x ∉ fieldScratch) (W : ℕ) (hw : a.env width = W)
    (hW : W < 2 ^ C.Wd) (hctx : 2 ≤ C.Wd) :
    Hs C (emitFields xs) a (xs.length * (18 * W + 15) + 1) (fun b =>
      b.out = a.out ++ xs.flatMap (fun x => frame (frame (binary W (a.env x)))) ∧
      outputRest b = outputRest a ∧ b.env width = W ∧ Cst b ∧ Fr a b fieldScratch) := by
  induction xs generalizing a with
  | nil =>
      refine (skip_spec a).mono (by simp) ?_
      rintro b rfl
      have hf : Fr a (a.set vJ 0) fieldScratch := Fr.set _ _ (by decide)
      exact ⟨by simp, rfl, by rw [hf _ (by decide)]; exact hw,
        Cst.of_fr hc hf (by decide), hf⟩
  | cons x xs ih =>
      unfold emitFields
      refine (Hs.seq (t2 := xs.length * (18 * W + 15) + 1)
        (emitFieldFrom_spec C a hc x (hxs x (by simp)) W hw hW hctx)
        fun b ⟨hbo, hbr, hbw, hbc, hbf⟩ => ?_).mono (by simp; ring_nf; omega) (fun _ h => h)
      refine (ih b hbc (fun y hy => hxs y (by simp [hy])) hbw).mono le_rfl ?_
      rintro d ⟨hdo, hdr, hdw, hdc, hdf⟩
      have he : xs.flatMap (fun y => frame (frame (binary W (b.env y)))) =
          xs.flatMap (fun y => frame (frame (binary W (a.env y)))) := by
        apply List.flatMap_congr
        intro y hy
        rw [hbf _ (hxs y (by simp [hy]))]
      exact ⟨by rw [hdo, hbo, he]; simp [List.append_assoc], hdr.trans hbr, hdw, hdc, Fr.trans hbf hdf⟩

/-- `lem:print`, paper/paper.tex: the exact marker body
of a framed unary family dimension. -/
def unaryBody (n : ℕ) : List Bool := (List.replicate n [true, true]).flatten

/-- `lem:print`, paper/paper.tex: each next unary
position appends its two physically emitted framing bits. -/
theorem unaryBody_succ (n : ℕ) : unaryBody (n + 1) = unaryBody n ++ [true, true] := by
  simp [unaryBody, List.replicate_succ']

/-- `lem:print`, paper/paper.tex: the unary marker
body and its delimiter are the exact complete original field. -/
theorem unaryBody_frame (n : ℕ) : unaryBody n ++ [false] = frame (List.replicate n true) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, show unaryBody (n + 1) = [true,true] ++ unaryBody n by
        simp [unaryBody, List.replicate_succ]]
      change [true,true] ++ (unaryBody n ++ [false]) = [true,true] ++ frame (List.replicate n true)
      rw [ih]

/-- `lem:print`, paper/paper.tex: unary dimensions are
written by a genuine counted loop followed by their literal delimiter. -/
def emitUnaryFrom (x : Fin VV) : St VV MM :=
  .seq (forS index x (StageLift.emitLiteral [true, true])) (.op (.emit false))

/-- `lem:print`, paper/paper.tex: actual unary family
metadata is generated in linear value time, without an encoded-field
premise or a random-access operation. -/
theorem emitUnaryFrom_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (x : Fin VV) (hx : index ≠ x) (hxj : x ≠ vJ) (n : ℕ) (hn : a.env x = n)
    (hfit : n < 2 ^ C.Wd) :
    Hs C (emitUnaryFrom x) a (9 * n + 6) (fun b =>
      b.out = a.out ++ frame (List.replicate n true) ∧ outputRest b = outputRest a ∧
      Cst b ∧ Fr a b [index, vJ]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.out = a.out ++ unaryBody k ∧ outputRest b = outputRest a ∧
      Cst b ∧ Fr a b [index, vJ]
  unfold emitUnaryFrom
  refine (Hs.seq (t2 := 1) (forS_spec' (C := C) index x hx (StageLift.emitLiteral [true, true])
    a n hfit I 5 ?_ ⟨by simp [unaryBody], rfl, hc, Fr.refl _ _⟩ hn ?_)
    fun b ⟨⟨hbo, hbr, hbc, hbf⟩, _, _⟩ => ?_).mono (by omega) (fun _ h => h)
  · intro k b val ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, Cst.of_fr (T := [index]) h3 (Fr.set _ _ (by decide)) (by decide),
      Fr.trans h4 (Fr.set _ _ (by simp))⟩
  · intro k hk b ⟨h1, h2, h3, h4⟩ hbi hbx
    refine (StageLift.emitLiteral_spec C [true, true] b h3).mono le_rfl ?_
    rintro d ⟨hd1, hd2, hd3, hd4⟩
    exact ⟨⟨by rw [hd1, h1, unaryBody_succ, List.append_assoc], hd2.trans h2, hd3,
      Fr.trans h4 (Fr.weaken hd4 (by simp))⟩,
      by rw [hd4 _ (by decide), hbi], by rw [hd4 _ (by simpa using hxj), hbx]⟩
  · refine (hs_emit C false b).mono le_rfl ?_
    rintro d rfl
    exact ⟨by rw [hbo, List.append_assoc, unaryBody_frame], hbr,
      ⟨hbc.z, hbc.one, hbc.two⟩, hbf⟩

end NearQuarticWires.StageRecovery.FixedBits
