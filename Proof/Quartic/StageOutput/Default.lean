import Proof.Quartic.StageOutput.Codec

/-!
# The encoded default-output branch

Paper: `sec:params`, paper/paper.tex, and
`sec:algorithm`. An already encoded pair of rationals is
copied after its branch tag. Each rational consists of three natural-number
words, so the pair uses six words.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

theorem natWord_member_length (xs : List ℕ) (v : ℕ) (hv : v ∈ xs) :
    (natWord v).length ≤ (xs.flatMap natWord).length := by
  induction xs with
  | nil => simp at hv
  | cons a xs ih =>
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · simp
    · have := ih hv
      simp only [List.flatMap_cons, List.length_append]
      omega

theorem copyNatsCost_le (xs : List ℕ) :
    copyNatsCost xs ≤ 80 * (xs.flatMap natWord).length + 1 := by
  induction xs with
  | nil => simp [copyNatsCost]
  | cons v xs ih =>
    have := natBitLength_pos v
    simp only [copyNatsCost, List.map_cons, List.sum_cons] at ih ⊢
    simp only [List.flatMap_cons, List.length_append, natWord_length]
    omega

/-- Discard the branch tag and copy exactly `n` encoded natural numbers. -/
def taggedCopy (n : ℕ) : St VV :=
  .seq constants (.seq rdc (copyNats n))

theorem taggedCopy_spec (tag : Bool) (xs : List ℕ) :
    Hs (ctxOf 4 (tag :: xs.flatMap natWord) []) (taggedCopy xs.length) a0
      (100 * ((tag :: xs.flatMap natWord).length + 1))
      (fun b => b.out = xs.flatMap natWord) := by
  let cw := tag :: xs.flatMap natWord
  let C := ctxOf 4 cw []
  have hWd : cw.length + 2 ≤ C.Wd := by
    change cw.length + 2 ≤ (cw.length + 4) ^ 4
    exact (by omega : cw.length + 2 ≤ cw.length + 4).trans
      (Nat.le_self_pow (by norm_num) _)
  have hL : cw.length + 2 < 2 ^ C.Wd := lt_of_le_of_lt hWd Nat.lt_two_pow_self
  have hW : ∀ v ∈ xs, natBitLength v + 2 ≤ C.Wd := by
    intro v hv
    have hm := natWord_member_length xs v hv
    rw [natWord_length] at hm
    have hlen : cw.length = (xs.flatMap natWord).length + 1 := rfl
    omega
  have hn := copyNatsCost_le xs
  change Hs C _ _ _ _
  refine Hs.mono (Hs.seq (t2 := 3 + copyNatsCost xs + 1)
    (constants_spec (C := C) (by omega)) (fun a ha => ?_)) (by dsimp [cw]; omega) (fun _ h => h)
  obtain ⟨hc, hcp, _, hout⟩ := ha
  refine Hs.seq (t2 := copyNatsCost xs)
    (rdc_spec a hc.pos (by change a.cp < cw.length; rw [hcp]; simp [cw]) (by change cw.length < _; omega)) (fun b hb => ?_)
  obtain ⟨_, hbpos, hbcp, _, hbout, hbfr⟩ := hb
  have hbc : Cst b := Cst.of_fr hc hbfr (by decide) (by rw [hbpos, hbcp])
  have hbin : C.cw.drop b.cp = xs.flatMap natWord ++ [] := by
    rw [hbcp, hcp]
    simp [C, cw, ctxOf]
  refine Hs.mono (copyNats_spec xs [] hW hL b hbc hbin) le_rfl ?_
  rintro d ⟨hd, _⟩
  rw [hd, hbout, hout, List.nil_append]

/-- The fixed six-word rational-pair copier as an ordinary word function. -/
noncomputable def defaultCodec :
    WordFunction {xs : List ℕ // xs.length = 6}
      (fun xs => frame (false :: xs.1.flatMap natWord) ++ frame [])
      (fun xs => xs.1.flatMap natWord)
      (fun xs => budgetOf VV 4 (false :: xs.1.flatMap natWord).length
        (100 * ((false :: xs.1.flatMap natWord).length + 1))) :=
  wordFunction_of_wmx (prog 4 (taggedCopy 6)) sOUT (by simp)
    (fun xs => capOf 4 (false :: xs.1.flatMap natWord) []
      (100 * ((false :: xs.1.flatMap natWord).length + 1))) (by
      intro xs
      obtain ⟨b, n, he, hn, hb⟩ := taggedCopy_spec false xs.1
      rw [xs.2] at he
      obtain ⟨τ, hrun, hout, hsh, hval⟩ := prog_spec 4 (by norm_num) (taggedCopy 6)
        (false :: xs.1.flatMap natWord) [] he _ hn
      exact ⟨τ, hrun, hout.trans hb, hsh, hval⟩)

end NearQuarticWires.StageOutput
