import Proof.Quartic.StageGamma.ConsRecipe

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: only unary
counts and fixed binary widths control the record-writer clock. -/
def Writer.counts : Writer → List (Fin VV)
  | .literal _ => []
  | .ruler count _ => [count]
  | .binary count _ _ => [count]
  | .seq first second => first.counts ++ second.counts
  | .nonzero _ body => body.counts

/-- `prop:time`, paper/paper.tex: a fixed numerical
constant records the exact finite control and marker-code overhead. -/
def Writer.clockFactor : Writer → ℕ
  | .literal bits => 2 * bits.length + 1
  | .ruler _ bits => 2 * bits.length + 9
  | .binary _ _ code => 2 * writerCodeWidth code + 16
  | .seq first second => first.clockFactor + second.clockFactor + 1
  | .nonzero _ body => body.clockFactor + 2

/-- `prop:time`, paper/paper.tex: no Gaussian
input producer runs for the numerical value of a field label; its clock
is linear in the widths and actual unary rulers only. -/
theorem Writer.cost_le (w : Writer) (a : DS VV MM) (B : ℕ)
    (hb : ∀ x ∈ w.counts, a.env x ≤ B) :
    w.cost a ≤ w.clockFactor * (B + 1) := by
  induction w with
  | literal bits => dsimp [cost, clockFactor]; nlinarith
  | ruler count bits =>
    have hc := hb count (by simp [counts])
    have hh := Nat.mul_le_mul_right (2 * bits.length + 5) hc
    dsimp [cost, clockFactor]
    nlinarith
  | binary count value code =>
    have hc := hb count (by simp [counts])
    have hh := Nat.mul_le_mul_right (2 * writerCodeWidth code + 10) hc
    dsimp [cost, clockFactor]
    nlinarith
  | seq first second hf hs =>
    have h1 := hf (fun x hx => hb x (by simp [counts, hx]))
    have h2 := hs (fun x hx => hb x (by simp [counts, hx]))
    dsimp [cost, clockFactor]
    nlinarith
  | nonzero test body ih =>
    have hh := ih hb
    dsimp [cost, clockFactor]
    nlinarith

/-- `prop:time`, paper/paper.tex: the actual full
31-port serializer loops only on ell, plen, the residual seed length,
and the projected cell width; there is no padded field-label loop. -/
theorem gammaBankWriter_counts : ∀ x : Fin VV, x ∈ gammaBankWriter.counts →
    x ∈ [requestFieldRegister 0, requestFieldRegister 3, gammaCellWidth, gammaRest] := by
  decide

/-- `prop:time`, paper/paper.tex: with the actual
ORIGINAL request widths, all Gaussian-input serialization costs are
bounded by a fixed constant times the actual seed length. -/
theorem gammaBankWriter_cost_le (request : Machine.GammaRequest) (a : DS VV MM)
    (he : a.env (requestFieldRegister 0) = request.parameters.ell)
    (hl : a.env (requestFieldRegister 3) = request.prefixLength)
    (hk : a.env gammaCellWidth = 2 * request.parameters.kh)
    (hr : a.env gammaRest = Cycle.seedLength request.parameters - request.prefixLength) :
    gammaBankWriter.cost a ≤ gammaBankWriter.clockFactor *
      (Cycle.seedLength request.parameters + 1) := by
  apply Writer.cost_le
  intro x hx
  have hm := gammaBankWriter_counts x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · rw [he]
    dsimp [Cycle.seedLength]
    omega
  · rw [hl]
    exact request.prefixFits
  · rw [hk]
    have := request.parameters.k_le
    dsimp [Cycle.seedLength]
    omega
  · rw [hr]
    exact Nat.sub_le _ _

end NearQuarticWires.StageGamma
