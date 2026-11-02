import Proof.Quartic.StageOutput.OutputBody

/-!
# The complete branch program for Step 5

Paper: `sec:params`, paper/paper.tex, and
`sec:algorithm`. The false tag is removed from an encoded
answer; the true tag selects the parsed arithmetic computation. One fixed
program handles both branches and every supplied padding length.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def outputProgram : St VV := .seq initializeTag
  (.ite (.eq t0 v1) trueOutputBody (copyNats 6))

def outputSteps (W : ℕ) : ℕ := 3000 * W + 3000

theorem outputProgram_spec {C : Ctx} (r : OutputRequest) (hr : r.Admissible)
    (hin : C.cw = r.padded) (hW : 64 * (C.cw.length + 1) ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C outputProgram a0 (outputSteps C.Wd) (fun b => b.out = outputWord r.result) := by
  cases r with
  | inl q =>
    have hlen : C.cw.length = (outputWord q).length + 1 := by rw [hin]; rfl
    have hvals : ∀ v ∈ rationalDigits q, natBitLength v + 2 ≤ C.Wd := by
      intro v hv
      have hh := natWord_member_length (rationalDigits q) v hv
      rw [rationalDigits_word, natWord_length] at hh
      omega
    have hcost := copyNatsCost_le (rationalDigits q)
    rw [rationalDigits_word] at hcost
    refine Hs.mono (Hs.seq (t2 := 2000 * C.Wd + 2001)
      (initializeTag_spec false (outputWord q) hin (by omega) (by omega))
      (fun a ha => ?_)) (by unfold outputSteps; omega) (fun _ h => h)
    obtain ⟨hc, _, ht, hp, _, ho⟩ := ha
    have he : (Cnd.eq t0 v1).eval a = false := by simp [Cnd.eval, ht, hc.one]
    have hi : C.cw.drop a.cp = (rationalDigits q).flatMap natWord ++ [] := by
      rw [hin, hp, rationalDigits_word]
      simp [OutputRequest.padded]
    have hcps := copyNats_spec (C := C) (rationalDigits q) [] hvals hL a hc hi
    rw [rationalDigits_length] at hcps
    refine Hs.mono (Hs.iteF (show t0 ≠ v1 by decide) he hcps) (by omega) ?_
    rintro b ⟨bo, _⟩
    simpa only [ho, List.nil_append, rationalDigits_word, OutputRequest.result] using bo
  | inr d =>
    refine Hs.mono (Hs.seq (t2 := 2000 * C.Wd + 2001)
      (initializeTag_spec true (d.word ++ List.replicate d.n false) hin (by omega) (by omega))
      (fun a ha => ?_)) (by unfold outputSteps; omega) (fun _ h => h)
    obtain ⟨hc, hv, ht, hp, _, ho⟩ := ha
    have he : (Cnd.eq t0 v1).eval a = true := by simp [Cnd.eval, ht, hc.one]
    have hi : C.cw.drop a.cp = d.word ++ List.replicate d.n false := by rw [hin, hp]; rfl
    refine Hs.mono (Hs.iteT (show t0 ≠ v1 by decide) he
      (trueOutputBody_spec d hr (by simpa only [hin, OutputRequest.padded] using hW)
        hL a hc hv _ hi)) le_rfl ?_
    intro b hb
    simpa only [ho, List.nil_append, OutputRequest.result] using hb

end NearQuarticWires.StageOutput
