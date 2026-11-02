import Proof.Quartic.StageOutput.DefaultRaw
import Proof.Quartic.StageOutput.PaddingTrue
import Proof.Quartic.StageOutput.Tag

/-!
# The two branches of explicit arithmetic allocation

Paper: `sec:params`, paper/paper.tex, and
`sec:algorithm`. Encoded answers are copied exactly.
Scalar requests are copied with `n` padding bits for the dyadic arithmetic.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

abbrev OutputRequest := Sum (ℚ × ℚ) Input

def OutputRequest.word : OutputRequest → List Bool
  | .inl q => false :: outputWord q
  | .inr d => true :: d.word

def OutputRequest.padded : OutputRequest → List Bool
  | .inl q => false :: outputWord q
  | .inr d => d.padded

def OutputRequest.padding : OutputRequest → ℕ
  | .inl _ => 0
  | .inr d => d.n

theorem readScalarsCost_le_word (fs : List (Fin VV × ℕ)) :
    readScalarsCost fs ≤ 40 * (fs.flatMap (fun xv => natWord xv.2)).length + 1 := by
  induction fs with
  | nil => simp [readScalarsCost]
  | cons p fs ih =>
    simp only [readScalarsCost, List.map_cons, List.sum_cons] at ih ⊢
    simp only [List.flatMap_cons, List.length_append, natWord_length]
    omega

theorem fieldWord_length (fs : List (Fin VV × ℕ)) (p : Fin VV × ℕ) (hp : p ∈ fs) :
    (natWord p.2).length ≤ (fs.flatMap (fun xv => natWord xv.2)).length := by
  have h := natWord_member_length (fs.map Prod.snd) p.2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  simpa only [List.flatMap_map, Function.comp_def] using h

def falsePaddingBody : St VV := .seq (.op (.emit false)) (copyNats 6)

theorem falsePaddingBody_spec {C : Ctx} (q : ℚ × ℚ)
    (hW : ∀ v ∈ rationalDigits q, natBitLength v + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (a : DS VV) (hc : Cst a) (hin : C.cw.drop a.cp = outputWord q) :
    Hs C falsePaddingBody a (copyNatsCost (rationalDigits q) + 2) (fun b =>
      b.out = a.out ++ (false :: outputWord q)) := by
  refine Hs.mono (Hs.seq (t2 := copyNatsCost (rationalDigits q)) (hs_emit C false a)
    (fun b hb => ?_)) (by omega) (fun _ h => h)
  subst hb
  have hc' : Cst {a with out := a.out ++ [false]} := ⟨hc.z, hc.one, hc.two, hc.pos⟩
  have hin' : C.cw.drop a.cp = (rationalDigits q).flatMap natWord ++ [] := by
    rw [rationalDigits_word, List.append_nil]
    exact hin
  have h := copyNats_spec (C := C) (rationalDigits q) [] hW hL _ hc' hin'
  rw [rationalDigits_length] at h
  refine Hs.mono h le_rfl ?_
  rintro b ⟨ho, _⟩
  rw [ho, rationalDigits_word]
  simp [List.append_assoc]

def paddingProgram : St VV := .seq initializeTag
  (.ite (.eq t0 v1) truePaddingBody falsePaddingBody)

def paddingSteps (r : OutputRequest) (W : ℕ) : ℕ := 1000 * W + 10 * r.padding + 3000

theorem paddingProgram_spec {C : Ctx} (r : OutputRequest)
    (hin : C.cw = r.word) (hW : C.cw.length + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C paddingProgram a0 (paddingSteps r C.Wd) (fun b => b.out = r.padded) := by
  cases r with
  | inl q =>
    have hlen : C.cw.length = (outputWord q).length + 1 := by rw [hin]; rfl
    have hvals : ∀ v ∈ rationalDigits q, natBitLength v + 2 ≤ C.Wd := by
      intro v hv
      have h := natWord_member_length (rationalDigits q) v hv
      rw [rationalDigits_word, natWord_length] at h
      omega
    have hcost := copyNatsCost_le (rationalDigits q)
    rw [rationalDigits_word] at hcost
    refine Hs.mono (Hs.seq (t2 := 900 * C.Wd + 2500)
      (initializeTag_spec false (outputWord q) hin (by omega) (by omega))
      (fun a ha => ?_)) (by simp [paddingSteps, OutputRequest.padding]; omega) (fun _ h => h)
    obtain ⟨hc, _, ht, hp, _, ho⟩ := ha
    have he : (Cnd.eq t0 v1).eval a = false := by simp [Cnd.eval, ht, hc.one]
    have hi : C.cw.drop a.cp = outputWord q := by rw [hin, hp]; rfl
    refine Hs.mono (Hs.iteF (show t0 ≠ v1 by decide) he (falsePaddingBody_spec q hvals hL a hc hi))
      (by omega) ?_
    intro b hb
    simpa only [ho, List.nil_append, OutputRequest.padded] using hb
  | inr d =>
    have hlen : C.cw.length = d.word.length + 1 := by rw [hin]; rfl
    have hvals : ∀ p ∈ d.fields, natBitLength p.2 + 2 ≤ C.Wd := by
      intro p hp
      have h := fieldWord_length d.fields p hp
      rw [natWord_length] at h
      change 2 * natBitLength p.2 + 1 ≤ d.word.length at h
      omega
    have hcost := readScalarsCost_le_word d.fields
    change readScalarsCost d.fields ≤ 40 * d.word.length + 1 at hcost
    refine Hs.mono (Hs.seq (t2 := 900 * C.Wd + 10 * d.n + 2500)
      (initializeTag_spec true d.word hin (by omega) (by omega))
      (fun a ha => ?_)) (by simp [paddingSteps, OutputRequest.padding]; omega) (fun _ h => h)
    obtain ⟨hc, hv, ht, hp, _, ho⟩ := ha
    have he : (Cnd.eq t0 v1).eval a = true := by simp [Cnd.eval, ht, hc.one]
    have hi : C.cw.drop a.cp = d.word ++ [] := by rw [hin, hp]; simp [OutputRequest.word]
    refine Hs.mono (Hs.iteT (show t0 ≠ v1 by decide) he
      (truePaddingBody_spec d hvals (by omega) hL a hc hv [] hi)) (by omega) ?_
    rintro b ⟨hb, _⟩
    simpa only [ho, List.nil_append, OutputRequest.padded] using hb

end NearQuarticWires.StageOutput
