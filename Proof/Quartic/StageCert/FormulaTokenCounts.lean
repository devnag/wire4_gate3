import Proof.Quartic.StagePrint.SelectedFormulas
import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open scoped BigOperators
open NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: a literal finite sum adds one token per summand and one
initial zero, without multiplying the sizes of its children. -/
theorem formulaListSum_tokens_le {V : ℕ} (fs : List (Formula V)) (B : ℕ)
    (h : ∀ f ∈ fs, (toks f).length ≤ B) :
    (toks (Mask.formulaListSum fs)).length ≤ fs.length*(B+1)+1 := by
  induction fs with
  | nil => simp [Mask.formulaListSum,toks]
  | cons f fs ih =>
    have hh := h f (by simp)
    have ht := ih (fun g hg=>h g (by simp [hg]))
    simp only [Mask.formulaListSum,toks,List.length_append,List.length_cons,List.length_nil,
      Nat.add_mul,Nat.one_mul]
    omega

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the literal finite product has additive token length. -/
theorem formulaListProd_tokens_le {V : ℕ} (fs : List (Formula V)) (B : ℕ)
    (h : ∀ f ∈ fs, (toks f).length ≤ B) :
    (toks (Mask.formulaListProd fs)).length ≤ fs.length*(B+1)+1 := by
  induction fs with
  | nil => simp [Mask.formulaListProd,toks]
  | cons f fs ih =>
    have hh := h f (by simp)
    have ht := ih (fun g hg=>h g (by simp [hg]))
    simp only [Mask.formulaListProd,toks,List.length_append,List.length_cons,List.length_nil,
      Nat.add_mul,Nat.one_mul]
    omega

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: each actual subset product has one more token than its
sum of factor-and-multiplication bounds. -/
theorem formulaProd_tokens_le {ι : Type*} {V : ℕ} (s : Finset ι)
    (f : ι → Formula V) (B : ℕ) (h : ∀ i ∈ s, (toks (f i)).length ≤ B) :
    (toks (Mask.formulaProd s f)).length ≤ s.card*(B+1)+1 := by
  classical
  unfold Mask.formulaProd
  apply (formulaListProd_tokens_le _ B ?_).trans
  · simp
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hg
    exact h i (by simpa using hi)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: an explicit finite sum has its actual cardinality cost. -/
theorem formulaSum_tokens_le {ι : Type*} {V : ℕ} (s : Finset ι)
    (f : ι → Formula V) (B : ℕ) (h : ∀ i ∈ s, (toks (f i)).length ≤ B) :
    (toks (Mask.formulaSum s f)).length ≤ s.card*(B+1)+1 := by
  classical
  unfold Mask.formulaSum
  apply (formulaListSum_tokens_le _ B ?_).trans
  · simp
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hg
    exact h i (by simpa using hi)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the original powerset mask may have exponentially many
tokens in `Xmax`; the displayed bound retains that construction cost. -/
theorem maskFormula_tokens_le {ι : Type*} [Fintype ι] {V : ℕ}
    (structural : Bool) (b : ι → Formula V) (tau Xmax T : ℕ)
    (hb : ∀ i, (toks (b i)).length ≤ T) :
    (toks (Mask.maskFormula structural b tau Xmax)).length ≤
      (Xmax+1)*((Fintype.card ι+1)^Xmax*(Xmax*(T+1)+2)+4)+3 := by
  classical
  have hp (a : ℕ) (ha : a ≤ Xmax) :
      (Finset.univ.powersetCard a : Finset (Finset ι)).card ≤
        (Fintype.card ι+1)^Xmax := by
    rw [Finset.card_powersetCard]
    exact (Nat.choose_le_pow _ _).trans
      ((Nat.pow_le_pow_left (by omega : Fintype.card ι ≤ Fintype.card ι+1) a).trans
        (Nat.pow_le_pow_right (by omega) ha))
  have inner (a : ℕ) (ha : a ≤ Xmax) :
      (toks (Mask.formulaSum (Finset.univ.powersetCard a)
        (fun s=>Mask.formulaProd s b))).length ≤
          (Fintype.card ι+1)^Xmax*(Xmax*(T+1)+2)+1 := by
    refine (formulaSum_tokens_le _ _ (Xmax*(T+1)+1) ?_).trans ?_
    · intro s hs
      have hs' := (Finset.mem_powersetCard.mp hs).2
      refine (formulaProd_tokens_le s b T (fun i _=>hb i)).trans ?_
      rw [hs']
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ ha) _
    · exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hp a ha)) _
  have hs := formulaSum_tokens_le (Finset.range (Xmax+1))
    (fun a=>Formula.mul (.const (Mask.newtonCoeff tau a))
      (Mask.formulaSum (Finset.univ.powersetCard a) (fun s=>Mask.formulaProd s b)))
    ((Fintype.card ι+1)^Xmax*(Xmax*(T+1)+2)+3) (by
      intro a ha
      have hh := inner a (by simpa using ha)
      simp only [toks,List.length_append,List.length_singleton]
      omega)
  simp only [Finset.card_range] at hs
  simp only [Mask.maskFormula,toks,List.length_append,List.length_singleton]
  convert Nat.add_le_add_left hs 2 using 1 <;> ring

/-- `lem:print`(c), paper/paper.tex: each selected
original mixed-residual square has at most eight postfix tokens. -/
theorem selectedSquare_tokens_le {m G : ℕ} (hm : 0 < m) (selection : Fin G→Bool)
    (edge : Fin (2*m)) (g : Fin G) :
    (toks (StagePrint.selectedSquare hm selection edge g)).length ≤ 8 := by
  unfold StagePrint.selectedSquare
  split <;> simp [toks,Cells.edgeFormula,Cells.deltaFormula]

/-- `lem:print`(c), paper/paper.tex: this is the
actual token-count bound for each retained-witness mask, on every column. -/
theorem selectedMask_tokens_le {m G : ℕ} (hm : 0 < m) (selection : Fin G→Bool)
    (structural : Bool) (edge : Fin (2*m)) (tau Xmax : ℕ) :
    (toks (StagePrint.selectedMaskFormula hm selection structural edge tau Xmax)).length ≤
      (Xmax+1)*((G+1)^Xmax*(9*Xmax+2)+4)+3 := by
  simpa only [StagePrint.selectedMaskFormula,Fintype.card_fin,Nat.mul_comm Xmax 9] using
    maskFormula_tokens_le structural (StagePrint.selectedSquare hm selection edge) tau Xmax 8
      (selectedSquare_tokens_le hm selection edge)

end NearQuarticWires.StageCert
