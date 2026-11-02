import Proof.Quartic.StageCert.MomentSyntax

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open Cells.ParameterArithmetic

/-- `lem:print` and `prop:time`, paper/paper.tex: all literal syntax parameters are included in the
actual physical source scale before any proposed column is tested. -/
theorem MomentRequest.syntax_parameters {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    (Builder.allGates r.call).length≤r.runtimeScale ∧
    r.selected.1.Xmax≤r.runtimeScale ∧ r.selected.1.k≤r.runtimeScale ∧
    r.coefficientBits≤r.runtimeScale ∧ r.atomBits≤r.runtimeScale := by
  have hb := r.runtimeScale_basic.2.1
  unfold MomentRequest.bodyScale at hb
  omega

private theorem tuple_size_scale (S P X G k : ℕ)
    (hS : 1≤S) (hP : 1≤P) (hX : X≤S) (hG : G≤S) (hk : k≤S) :
    8*((X+1)*(P*(11*X+4)+4)+4)+82*G+8*k+4≤1000*S^3*P := by
  have hs2 : 1≤S^2 := Nat.pow_pos hS
  have hs3 : S≤S^3 := Nat.le_self_pow (by decide) _
  have hs23 : S^2≤S^3 := Nat.pow_le_pow_right hS (by decide)
  have hSP : S≤S*P := Nat.le_mul_of_pos_right _ hP
  have hSP3 : S≤S^3*P := hs3.trans (Nat.le_mul_of_pos_right _ hP)
  have h1 : X+1≤2*S := by omega
  have h2 : 11*X+4≤15*S := by omega
  have h3 : P*(11*X+4)+4≤19*S*P := by nlinarith only [Nat.mul_le_mul_left P h2,hSP,hS]
  have h4 : (X+1)*(P*(11*X+4)+4)+4≤42*S^2*P := by
    have hh := Nat.mul_le_mul h1 h3
    have hp : 1≤S^2*P := Nat.mul_pos hs2 hP
    nlinarith only [hh,hp]
  have h5 : (X+1)*(P*(11*X+4)+4)+4≤42*S^3*P :=
    h4.trans (Nat.mul_le_mul_right P (Nat.mul_le_mul_left 42 hs23))
  have hp : 1≤S^3*P := Nat.mul_pos (Nat.pow_pos hS) hP
  nlinarith only [h5,hG,hk,hSP3,hp]

private theorem tuple_weight_scale (S P X G k C : ℕ)
    (hS : 1≤S) (hP : 1≤P) (hX : X≤S) (hG : G≤S) (hk : k≤S) (hC : C≤S) :
    8*(1+(X+1)*(X+2+P*(8*X+3)))+1+8*k*(G*(8*(C+5)+1))≤1000*S^3*P := by
  have hs2 : 1≤S^2 := Nat.pow_pos hS
  have hs23 : S^2≤S^3 := Nat.pow_le_pow_right hS (by decide)
  have hSP : S≤S*P := Nat.le_mul_of_pos_right _ hP
  have h1 : X+1≤2*S := by omega
  have h2 : 8*X+3≤11*S := by omega
  have h3 : X+2+P*(8*X+3)≤14*S*P := by
    nlinarith only [Nat.mul_le_mul_left P h2,hSP,hX,hS]
  have h4 : 1+(X+1)*(X+2+P*(8*X+3))≤29*S^2*P := by
    have hh := Nat.mul_le_mul h1 h3
    have hp : 1≤S^2*P := Nat.mul_pos hs2 hP
    nlinarith only [hh,hp]
  have h5 := h4.trans (Nat.mul_le_mul_right P (Nat.mul_le_mul_left 29 hs23))
  have hc : 8*(C+5)+1≤49*S := by omega
  have h6 : 8*k*(G*(8*(C+5)+1))≤392*S^3 := by
    calc
      _≤8*S*(S*(49*S)) := by gcongr
      _=392*S^3 := by ring
  have h7 : 8*k*(G*(8*(C+5)+1))≤392*S^3*P :=
    h6.trans (Nat.le_mul_of_pos_right _ hP)
  have hp : 1≤S^3*P := Nat.mul_pos (Nat.pow_pos hS) hP
  nlinarith only [h5,h7,hp]

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual tuple trees' size and construction weight
are bounded by their displayed tuple count times a cubic source scale. -/
theorem MomentRequest.syntax_scale {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.formula.size≤1000*r.runtimeScale^3*((Builder.allGates r.call).length+1)^r.selected.1.Xmax ∧
    r.formula.weight≤1000*r.runtimeScale^3*((Builder.allGates r.call).length+1)^r.selected.1.Xmax := by
  have hS : 1≤r.runtimeScale := by have hh := r.runtimeScale_basic.1; omega
  have hP : 1≤((Builder.allGates r.call).length+1)^r.selected.1.Xmax := Nat.pow_pos (Nat.succ_pos _)
  obtain ⟨hG,hX,hk,hC,_⟩ := r.syntax_parameters
  exact ⟨r.formula_size_bound.trans (tuple_size_scale _ _ _ _ _ hS hP hX hG hk),
    r.formula_weight_bound.trans (tuple_weight_scale _ _ _ _ _ _ hS hP hX hG hk hC)⟩

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact raw signed codec, actual syntax and
construction weight fit a fourth scale power with the literal tuple factor. -/
theorem MomentRequest.raw_formula_source_scale {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    (formulaWord ⟨17*(Builder.allGates r.call).length,r.formula⟩).length+
      r.formula.size+r.formula.weight+1≤
      100000*r.runtimeScale^4*((Builder.allGates r.call).length+1)^r.selected.1.Xmax := by
  let S := r.runtimeScale
  let P := ((Builder.allGates r.call).length+1)^r.selected.1.Xmax
  let L := r.selected.1.Xmax+r.coefficientBits+2
  have hS : 1≤S := by have hh := r.runtimeScale_basic.1; omega
  have hP : 1≤P := Nat.pow_pos (Nat.succ_pos _)
  obtain ⟨_,hX,_,hC,hA⟩ := r.syntax_parameters
  have hL : L≤4*S := by dsimp only [L]; omega
  have hb := cert_raw_formula_word_bytes r.formula L r.formula_constant_bits
  change (formulaWord ⟨17*(Builder.allGates r.call).length,r.formula⟩).length≤
    (2*(r.atomBits+L+1)+17)*r.formula.size+2*r.atomBits+4 at hb
  have hpre : 2*(r.atomBits+L+1)+17≤29*S := by change r.atomBits≤S at hA; omega
  obtain ⟨hsize,hweight⟩ := r.syntax_scale
  change r.formula.size≤1000*S^3*P at hsize
  change r.formula.weight≤1000*S^3*P at hweight
  have hmul := Nat.mul_le_mul hpre hsize
  have hs34 : S^3≤S^4 := Nat.pow_le_pow_right hS (by decide)
  have hsize4 := hsize.trans (Nat.mul_le_mul_right P (Nat.mul_le_mul_left 1000 hs34))
  have hweight4 := hweight.trans (Nat.mul_le_mul_right P (Nat.mul_le_mul_left 1000 hs34))
  have hS4 : S≤S^4*P := (Nat.le_self_pow (by decide) _).trans (Nat.le_mul_of_pos_right _ hP)
  have h14 : 1≤S^4*P := Nat.mul_pos (Nat.pow_pos hS) hP
  have he : 29*S*(1000*S^3*P)=29000*S^4*P := by ring
  rw [he] at hmul
  change _≤100000*S^4*P
  change r.atomBits≤S at hA
  nlinarith only [hb,hmul,hsize4,hweight4,hS4,h14,hA]

end NearQuarticWires.StageCert.Tokens
