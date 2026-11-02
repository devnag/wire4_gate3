import Proof.Quartic.StageGamma.BinaryEmit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTablesProg

/-- `cor:conditional`, paper/paper.tex: fixed-control
input records contain literal markers, binary payloads and unary rulers. -/
inductive Writer where
  | literal (bits : List Bool)
  | ruler (count : Fin VV) (bits : List Bool)
  | binary (count value : Fin VV) (code : Bool → List Bool)
  | seq (first second : Writer)
  | nonzero (test : Fin VV) (body : Writer)

/-- `cor:conditional`, paper/paper.tex: all physical
scratch variables of the Gaussian input serializer. -/
def writerScratch : List (Fin VV) := emitIndex :: binaryScratch

/-- `cor:conditional`, paper/paper.tex: register
parameters of a fixed Gaussian input serializer. -/
def Writer.params : Writer → List (Fin VV)
  | .literal _ => []
  | .ruler count _ => [count]
  | .binary count value _ => [count, value]
  | .seq first second => first.params ++ second.params
  | .nonzero test body => test :: body.params

/-- `cor:conditional`, paper/paper.tex: source
registers are disjoint from serializer scratch, including every branch. -/
def Writer.Safe : Writer → Prop
  | .literal _ => True
  | .ruler count _ => count ∉ writerScratch
  | .binary count value _ => count ∉ writerScratch ∧ value ∉ writerScratch
  | .seq first second => first.Safe ∧ second.Safe
  | .nonzero test body => test ∉ writerScratch ∧ test ≠ vZ ∧ body.Safe

/-- `prop:time`, paper/paper.tex: the constant
number of actual output bits emitted for one computed payload bit. -/
def writerCodeWidth (code : Bool → List Bool) : ℕ :=
  max (code false).length (code true).length

/-- `cor:conditional`, paper/paper.tex: the exact
source word generated from the decoded registers. -/
def Writer.bits (a : DS VV MM) : Writer → List Bool
  | .literal bits => bits
  | .ruler count bits => bitBlocks bits (a.env count)
  | .binary count value code =>
      ((List.range (a.env count)).map (a.env value).testBit).flatMap code
  | .seq first second => first.bits a ++ second.bits a
  | .nonzero test body => if a.env test = 0 then [] else body.bits a

/-- `prop:time`, paper/paper.tex: an explicit
physical source-language clock also bounds the emitted input length. -/
def Writer.cost (a : DS VV MM) : Writer → ℕ
  | .literal bits => 2 * bits.length + 1
  | .ruler count bits => a.env count * (2 * bits.length + 5) + 4
  | .binary count _ code => a.env count * (2 * writerCodeWidth code + 10) + 6
  | .seq first second => first.cost a + second.cost a + 1
  | .nonzero _ body => body.cost a + 2

/-- `cor:conditional`, paper/paper.tex: one finite
ordinary control program implements the complete record recipe. -/
def Writer.program : Writer → St VV MM
  | .literal bits => emitBits bits
  | .ruler count bits => emitRepeated count bits
  | .binary count value code => binaryEmit count value code
  | .seq first second => .seq first.program second.program
  | .nonzero test body => .ite (.eq test vZ) skipS body.program

/-- `cor:conditional`, paper/paper.tex: every used
source register is protected from the actual serializer scratch. -/
theorem Writer.safe_params (w : Writer) (hs : w.Safe) :
    ∀ x ∈ w.params, x ∉ writerScratch := by
  induction w with
  | literal bits => simp [params]
  | ruler count bits => simpa [params, Safe] using hs
  | binary count value code => simpa [params, Safe] using hs
  | seq first second hfirst hsecond =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hfirst hs.1 x hx
    · exact hsecond hs.2 x hx
  | nonzero test body ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hs.1
    · exact ih hs.2.2 x hx

/-- `cor:conditional`, paper/paper.tex: serializer
scratch changes neither its source recipe nor its charged clock. -/
theorem Writer.stable (w : Writer) (hs : w.Safe) (a b : DS VV MM)
    (hf : Fr a b writerScratch) : w.bits b = w.bits a ∧ w.cost b = w.cost a := by
  induction w with
  | literal payload => exact ⟨rfl, rfl⟩
  | ruler count payload => simp only [Writer.bits, cost, hf count hs, and_self]
  | binary count value code =>
    simp only [Writer.bits, cost, hf count hs.1, hf value hs.2, and_self]
  | seq first second hfirst hsecond =>
    obtain ⟨hfb, hfc⟩ := hfirst hs.1
    obtain ⟨hsb, hsc⟩ := hsecond hs.2
    exact ⟨by simp only [bits, hfb, hsb], by simp only [cost, hfc, hsc]⟩
  | nonzero test body ih =>
    obtain ⟨hb, hc⟩ := ih hs.2.2
    exact ⟨by simp only [bits, hf test hs.1, hb], by simp only [cost, hc]⟩

/-- `prop:time`, paper/paper.tex: actual printed
source bits fit within the source-language execution charge. -/
theorem Writer.length_le_cost (w : Writer) (a : DS VV MM) :
    (w.bits a).length ≤ w.cost a := by
  induction w with
  | literal payload => simp only [Writer.bits, cost]; omega
  | ruler count payload => simp only [bits, cost, bitBlocks_length]; nlinarith
  | binary count value code =>
    have hh := coded_length_le code (writerCodeWidth code) (by
      intro bit; cases bit <;> simp [writerCodeWidth])
      ((List.range (a.env count)).map (a.env value).testBit)
    simp only [List.length_map, List.length_range] at hh
    simp only [bits, cost]
    nlinarith
  | seq first second hf hs => simp only [bits, cost, List.length_append]; omega
  | nonzero test body ih =>
    simp only [bits, cost]
    split_ifs
    · simp
    · omega

/-- `cor:conditional` and `prop:time`, paper/paper.tex: exact physical Gaussian record generation, with all
markers, payload bits, conditional records and rulers paid. -/
theorem Writer.run (w : Writer) (hs : w.Safe) (C : Ctx) (a : DS VV MM)
    (hc : Cst a) (hW : 2 ≤ C.Wd)
    (hfit : ∀ x ∈ w.params, a.env x < 2 ^ C.Wd)
    (hroom : a.kin.length + w.cost a ≤ C.Lk) :
    Hs C w.program a (w.cost a) (fun b =>
      b.kin = a.kin ++ w.bits a ∧ SameN a b ∧ Cst b ∧ Fr a b writerScratch) := by
  induction w generalizing a with
  | literal bits =>
    refine Hs.mono (emitBits_spec C bits a hc (by dsimp [cost] at hroom; omega)) le_rfl ?_
    intro b ⟨hb, hsame, hbc, hfr⟩
    exact ⟨hb, hsame, hbc, hfr.weaken (by simp [writerScratch, binaryScratch])⟩
  | ruler count payload =>
    have hcount : count ∉ binaryScratch := fun h => hs (by simp [writerScratch, h])
    have hj : count ≠ vJ := by intro h; exact hs (by simp [writerScratch, binaryScratch, h])
    have he : emitIndex ≠ count := by intro h; exact hs (by simp [writerScratch, h])
    refine Hs.mono (emitRepeated_spec C count he hj payload a hc (a.env count) rfl
      (hfit count (by simp [params])) (by dsimp [cost] at hroom; nlinarith)) le_rfl ?_
    intro b ⟨hb, hsame, hbc, hfr⟩
    exact ⟨hb, hsame, hbc, hfr.weaken (by simp [writerScratch, binaryScratch])⟩
  | binary count value code =>
    have hcount : count ∉ binaryScratch := fun h => hs.1 (by simp [writerScratch, h])
    have hvalue : value ∉ binaryScratch := fun h => hs.2 (by simp [writerScratch, h])
    refine Hs.mono (binaryEmit_spec C count value hcount hvalue code (writerCodeWidth code)
      (by intro bit; cases bit <;> simp [writerCodeWidth]) a hc hW (a.env count) (a.env value)
      rfl rfl (hfit count (by simp [params])) (by dsimp [cost] at hroom; nlinarith)) le_rfl ?_
    intro b ⟨hb, hsame, hbc, hfr⟩
    exact ⟨hb, hsame, hbc, hfr.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy)⟩
  | seq first second hfirst hsecond =>
    refine Hs.seq (t1 := first.cost a) (t2 := second.cost a)
      (hfirst hs.1 a hc (fun x hx => hfit x (by simp [params, hx]))
        (by dsimp [cost] at hroom; omega)) ?_
    intro b ⟨hb, hsame, hbc, hfr⟩
    obtain ⟨hbits, hcost⟩ := second.stable hs.2 a b hfr
    have hf : ∀ x ∈ second.params, b.env x < 2 ^ C.Wd := by
      intro x hx
      rw [hfr x (second.safe_params hs.2 x hx)]
      exact hfit x (by simp [params, hx])
    have hr : b.kin.length + second.cost b ≤ C.Lk := by
      rw [hb, List.length_append, hcost]
      have := first.length_le_cost a
      dsimp [cost] at hroom
      omega
    refine Hs.mono (hsecond hs.2 b hbc hf hr) (by rw [hcost]) ?_
    intro e ⟨he, hes, hec, hef⟩
    exact ⟨by rw [he, hb, hbits]; simp only [bits, List.append_assoc],
      hsame.trans hes, hec, hfr.trans hef⟩
  | nonzero test body ih =>
    refine Hs.ite (c := .eq test vZ) (t := body.cost a + 1) hs.2.1 ?_ ?_
    · intro hz
      have hz' : a.env test = 0 := by simpa [Cnd.eval, hc.z] using hz
      refine Hs.mono (skip_spec a) (by omega) ?_
      rintro b rfl
      exact ⟨by simp [bits, hz', DS.set], SameN.set _ _ _,
        Cst.of_fr (T := [vJ]) hc (Fr.set _ _ (by simp)) (by decide),
        Fr.set _ _ (by simp [writerScratch, binaryScratch])⟩
    · intro hn
      have hn' : a.env test ≠ 0 := by simpa [Cnd.eval, hc.z] using hn
      refine Hs.mono (ih hs.2.2 a hc (fun x hx => hfit x (by simp [params, hx]))
        (by dsimp [cost] at hroom; omega)) (by omega) ?_
      intro b hb
      simpa [bits, hn'] using hb

end NearQuarticWires.StageGamma
