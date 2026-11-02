import Proof.Quartic.StageOutput.Parse

/-!
# The thirteen binary fields of Step 5

Paper: `sec:algorithm`, paper/paper.tex. The nine semantic
inputs include one rational number and two signed totals. With nonnegative
totals and error parameter, their sign fields are zero; consistency is
encoded as the natural number zero or one.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch

structure Input where
  n : ℕ
  k : ℕ
  Q : ℕ
  MF : ℕ
  etaNum : ℕ
  etaDen : ℕ
  nc : ℕ
  consistent : Bool
  A : ℕ
  M : ℕ

def Input.fields (d : Input) : List (Fin VV × ℕ) :=
  [(20, d.n), (21, d.k), (22, d.Q), (23, d.MF), (24, 0),
   (25, d.etaNum), (26, d.etaDen), (27, d.nc), (28, d.consistent.toNat),
   (29, 0), (30, d.A), (31, 0), (32, d.M)]

def Input.word (d : Input) : List Bool := d.fields.flatMap (fun xv => natWord xv.2)

def inputVariables : List (Fin VV) := [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]

def Input.Stored (d : Input) (env : Fin VV → ℕ) : Prop :=
  env 20 = d.n ∧ env 21 = d.k ∧ env 22 = d.Q ∧ env 23 = d.MF ∧ env 24 = 0 ∧
  env 25 = d.etaNum ∧ env 26 = d.etaDen ∧ env 27 = d.nc ∧ env 28 = d.consistent.toNat ∧
  env 29 = 0 ∧ env 30 = d.A ∧ env 31 = 0 ∧ env 32 = d.M

theorem Input.fields_stored (d : Input) (env : Fin VV → ℕ) : d.Stored (fieldEnv d.fields env) := by
  simp [Input.Stored, Input.fields, fieldEnv]

theorem Input.stored_word (d : Input) {env : Fin VV → ℕ} (h : d.Stored env) :
    inputVariables.flatMap (fun x => natWord (env x)) = d.word := by
  obtain ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩ := h
  simp [inputVariables, Input.word, Input.fields, h20, h21, h22, h23, h24,
    h25, h26, h27, h28, h29, h30, h31, h32]

theorem Input.word_length_pos (d : Input) : 0 < d.word.length := by
  have := natBitLength_pos d.n
  simp only [Input.word, Input.fields, List.flatMap_cons, List.flatMap_nil,
    List.length_append, natWord_length, List.length_nil]
  omega

/-- Parse every scalar once, retaining the exact order and cursor advance. -/
def parseInput : St VV := readScalars inputVariables

theorem parseInput_spec {C : Ctx} (d : Input)
    (hW : ∀ xv ∈ d.fields, natBitLength xv.2 + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (a : DS VV) (hc : Cst a) (rest : List Bool) (hin : C.cw.drop a.cp = d.word ++ rest) :
    Hs C parseInput a (readScalarsCost d.fields) (fun b =>
      d.Stored b.env ∧ b.cp = a.cp + d.word.length ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧
      ∀ y : Fin VV, 15 ≤ y.val → b.env y = fieldEnv d.fields a.env y) := by
  have hx : ∀ xv ∈ d.fields, 15 ≤ xv.1.val := by
    intro xv hx
    simp only [Input.fields, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have h := readScalars_spec d.fields hx hW hL rest a hc hin
  have hvars : d.fields.map Prod.fst = inputVariables := rfl
  rw [hvars] at h
  refine Hs.mono h le_rfl ?_
  rintro b ⟨hcp, hwq, hout, hbc, henv⟩
  refine ⟨?_, hcp, hwq, hout, hbc, henv⟩
  have hs := d.fields_stored a.env
  simp only [Input.Stored] at hs ⊢
  simpa only [henv 20 (by decide), henv 21 (by decide), henv 22 (by decide), henv 23 (by decide),
    henv 24 (by decide), henv 25 (by decide), henv 26 (by decide), henv 27 (by decide),
    henv 28 (by decide), henv 29 (by decide), henv 30 (by decide), henv 31 (by decide), henv 32 (by decide)] using hs

end NearQuarticWires.StageOutput
