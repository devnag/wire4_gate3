# Modular discrete tomography (`thm:modular-tomography`)

[Mapping index](README.md) · a result of independent interest · no published premise

The theorem does not mention circuits. Its Lean form is in
[Proof/Quartic/Tomography.lean](../Proof/Quartic/Tomography.lean) (namespace `NearQuarticWires.Tomography`), proved
from the near-cubic gate companion's `NearCubicGates.Reconstruction.pairMatrix_injective` and
`pair_reconstruction_complete` ([PairReconstruction.lean](../Proof/Gates/PairReconstruction.lean)).
[Check.lean](../Check.lean) prints the axioms of these theorems and fails unless they are `propext`,
`Classical.choice` and `Quot.sound`. Other work can use them with `import Proof.Quartic.Tomography`.

<!-- files -->
**Files.** The line numbers below are of these files:

- [`paper/paper.tex`](../paper/paper.tex), SHA-256 `32c365c3c97134031d57cc7fe42432513408376fadb04ada31f3a9205b38070e`
- [`Proof/Gates/ScalarWindow.lean`](../Proof/Gates/ScalarWindow.lean), SHA-256 `c905aaac3d96944127d2f3426627a68402078da0c4fb0fc5225e2aa228a39366`
- [`Proof/Gates/TomographyDirections.lean`](../Proof/Gates/TomographyDirections.lean), SHA-256 `f68e8ef128821e7111b190c52d26643e80eb8d9314102da04cde92c4b25f37ff`
- [`Proof/Quartic/Tomography.lean`](../Proof/Quartic/Tomography.lean), SHA-256 `328f29b4e1a7e0da4e1ec433832d576b47693b55d5e1c0abedc785e3cadce334`
<!-- /files -->

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>

<!-- paper file=paper/paper.tex label=thm:modular-tomography -->
<b>paper/paper.tex, lines 544–549</b> ([paper/paper.tex](../paper/paper.tex#L544-L549))

<pre>
\begin{theorem}[Modular discrete tomography]\label{thm:modular-tomography}
Let \(\mathcal P\) be a finite nonempty set of primes, \(D'=1+\sum_{p\in\mathcal P}(p-1)\), and \(S(q)=\sum_{m=1}^{q}m\varphi(m)\), where \(\varphi\) is Euler's totient.
For \(a,b\in\Z\) and \(L\in\N\) with \(2\le L\le S(\lfloor(D'-1)/(L-1)\rfloor)\), every \(f:B\to\Q\) on the known box \(B=([a,a+L)\times[b,b+L))\cap\Z^2\) is determined by its exact rational sums
\(F_p(r,s)=\sum_{(x,y)\in B,\;(x,y)\equiv(r,s)\bmod p}f(x,y)\), for \(p\in\mathcal P\), \(r,s\in\Z/p\Z\).
Exact elimination recovers \(f\) in time polynomial in \(L\), \(\sum_{p\in\mathcal P}p^2\), and the total binary input length, including the box endpoints and rational sums.
\end{theorem}
</pre>
<!-- /paper -->

</td><td>

<!-- lean NearCubicGates.ScalarWindow.window -->
[Proof/Gates/ScalarWindow.lean, lines 21–22](../Proof/Gates/ScalarWindow.lean#L21-L22)

<pre title="Proof/Gates/ScalarWindow.lean, lines 21–22">
/-- The exact scalar distributional window of `lem:one-window`. -/
def window (primes : Finset ℕ) : ℕ := 1 + ∑ p ∈ primes, (p - 1)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.TomographyDirections.degreeSum -->
[Proof/Gates/TomographyDirections.lean, lines 73–74](../Proof/Gates/TomographyDirections.lean#L73-L74)

<pre title="Proof/Gates/TomographyDirections.lean, lines 73–74">
/-- `S(q)` from the quantitative reconstruction criterion, with `S(0)=0`. -/
def degreeSum (q : ℕ) : ℕ := ∑ m ∈ Finset.Icc 1 q, m * Nat.totient m
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Tomography.residueCounts -->
[Proof/Quartic/Tomography.lean, lines 37–42](../Proof/Quartic/Tomography.lean#L37-L42)

<pre title="Proof/Quartic/Tomography.lean, lines 37–42">
/-- The residue counts of `f` on the box with corner `(lo₁, lo₂)` and side `L`, for the primes of `primes`: at the
row `⟨p, (a, b)⟩` the sum of `f` over the points `(lo₁ + x, lo₂ + y)` of the box with `lo₁ + x ≡ a` and
`lo₂ + y ≡ b (mod p)` (`residueCounts_apply`). -/
def residueCounts (primes : Finset ℕ) (lo₁ lo₂ : ℤ) (L : ℕ) (f : Fin L × Fin L → ℚ) :
    PairResidueRow (fun p : primes =&gt; p.val) → ℚ :=
  pairMatrix primes lo₁ lo₂ L *ᵥ f
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Tomography.residueCounts_apply -->
[Proof/Quartic/Tomography.lean, lines 44–51](../Proof/Quartic/Tomography.lean#L44-L51)

<pre title="Proof/Quartic/Tomography.lean, lines 44–51">
/-- The residue counts, pointwise. -/
theorem residueCounts_apply (primes : Finset ℕ) (lo₁ lo₂ : ℤ) (L : ℕ) (f : Fin L × Fin L → ℚ)
    (p : primes) (a b : Fin p.val) :
    residueCounts primes lo₁ lo₂ L f ⟨p, (a, b)⟩ =
      ∑ i : Fin L × Fin L,
        if (lo₁ + (i.1.val : ℤ)) % (p.val : ℤ) = (a.val : ℤ) ∧
            (lo₂ + (i.2.val : ℤ)) % (p.val : ℤ) = (b.val : ℤ) then f i else 0 := by
  simp only [residueCounts, pairMatrix, pairResidueMatrix, Matrix.mulVec, dotProduct, ite_mul, one_mul, zero_mul]
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Tomography.residueCounts_determine -->
[Proof/Quartic/Tomography.lean, lines 53–60](../Proof/Quartic/Tomography.lean#L53-L60)

<pre title="Proof/Quartic/Tomography.lean, lines 53–60">
/-- **Residue counts determine the function.** For a nonempty finite set of primes with window
`W = 1 + Σ_p (p − 1)` and a side `2 ≤ L ≤ S(⌊(W − 1)/(L − 1)⌋)`, two rational functions on an `L × L` integer box
with the same residue counts are equal. -/
theorem residueCounts_determine (primes : Finset ℕ) (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo₁ lo₂ : ℤ) (L : ℕ) (hL : 2 ≤ L) (hsize : L ≤ degreeSum ((window primes - 1) / (L - 1)))
    {f g : Fin L × Fin L → ℚ} (h : residueCounts primes lo₁ lo₂ L f = residueCounts primes lo₁ lo₂ L g) :
    f = g :=
  pairMatrix_injective primes hne hprime lo₁ lo₂ L hL hsize h
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Tomography.reconstruct -->
[Proof/Quartic/Tomography.lean, lines 62–70](../Proof/Quartic/Tomography.lean#L62-L70)

<pre title="Proof/Quartic/Tomography.lean, lines 62–70">
/-- **Reconstruction.** Under the hypotheses of `residueCounts_determine`, a rational left inverse `R` of the count
matrix exists, is accepted by the exact check `leftInverseCheck`, and recovers every function from its residue
counts. -/
theorem reconstruct (primes : Finset ℕ) (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo₁ lo₂ : ℤ) (L : ℕ) (hL : 2 ≤ L) (hsize : L ≤ degreeSum ((window primes - 1) / (L - 1))) :
    ∃ R : Matrix (Fin L × Fin L) (PairResidueRow (fun p : primes =&gt; p.val)) ℚ,
      leftInverseCheck (pairMatrix primes lo₁ lo₂ L) R = true ∧
      ∀ f : Fin L × Fin L → ℚ, R *ᵥ residueCounts primes lo₁ lo₂ L f = f :=
  pair_reconstruction_complete primes hne hprime lo₁ lo₂ L hL hsize
</pre>
<!-- /lean -->

</td></tr>
<tr><td>

<!-- paper file=paper/paper.tex label=cor:prime-window-tomography -->
<b>paper/paper.tex, lines 558–560</b> ([paper/paper.tex](../paper/paper.tex#L558-L560))

<pre>
\begin{corollary}[Prime-window tomography]\label{cor:prime-window-tomography}
There are absolute constants \(c&gt;0\) and \(P_0\) such that, for every integer \(P\ge P_0\), taking \(\mathcal P\) to be all primes in \((P/2,P]\), \cref{thm:modular-tomography} applies to every known integer box of side \(2\le L\le cP^{3/2}/(\log P)^{3/4}\).
\end{corollary}
</pre>
<!-- /paper -->

</td><td>

<!-- lean NearQuarticWires.Tomography.side_bounds -->
[Proof/Quartic/Tomography.lean, lines 72–75](../Proof/Quartic/Tomography.lean#L72-L75)

<pre title="Proof/Quartic/Tomography.lean, lines 72–75">
/-- The computable side `side W = ⌊⌊√⌊√W⌋⌋³/24⌋` is of order `W^{3/4}`. -/
theorem side_bounds (W : ℕ) (hW : 4 ^ 4 ≤ W) :
    QuantitativePairWindow.side W ^ 4 ≤ W ^ 3 ∧ W ^ 3 ≤ (16 ^ 3 * 48 ^ 4) * QuantitativePairWindow.side W ^ 4 :=
  QuantitativePairWindow.side_three_quarters W hW
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Tomography.reconstruct_at_side -->
[Proof/Quartic/Tomography.lean, lines 77–90](../Proof/Quartic/Tomography.lean#L77-L90)

<pre title="Proof/Quartic/Tomography.lean, lines 77–90">
/-- **Reconstruction at side of order `W^{3/4}`.** For every nonempty finite set of primes whose window `W` is large
enough, every rational function on a box of side `side W` is recovered from its residue counts by a checked rational
left inverse. -/
theorem reconstruct_at_side :
    ∃ onset : ℕ, ∀ (primes : Finset ℕ), primes.Nonempty → (∀ p ∈ primes, Nat.Prime p) →
      onset ^ 4 ≤ window primes → ∀ lo₁ lo₂ : ℤ,
      ∃ R : Matrix (Fin (QuantitativePairWindow.side (window primes)) × Fin (QuantitativePairWindow.side (window primes)))
          (PairResidueRow (fun p : primes =&gt; p.val)) ℚ,
        leftInverseCheck (pairMatrix primes lo₁ lo₂ (QuantitativePairWindow.side (window primes))) R = true ∧
        ∀ f, R *ᵥ residueCounts primes lo₁ lo₂ (QuantitativePairWindow.side (window primes)) f = f := by
  obtain ⟨onset, _, h⟩ := QuantitativePairWindow.side_is_admissible
  refine ⟨onset, fun primes hne hprime hW lo₁ lo₂ =&gt; ?_⟩
  obtain ⟨hL, hsize⟩ := h (window primes) hW
  exact reconstruct primes hne hprime lo₁ lo₂ _ hL hsize
</pre>
<!-- /lean -->

</td></tr>
</table>

## What to check

1. **The box.** The paper's `B = ([a, a+L) × [b, b+L)) ∩ ℤ²` is indexed in Lean by `Fin L × Fin L`, the index
   `(x, y)` standing for the point `(lo₁ + x, lo₂ + y)` with `lo₁ = a`, `lo₂ = b`.
2. **The counts.** `F_p(r, s)` is `residueCounts P lo₁ lo₂ L f ⟨p, (r, s)⟩`: the sum of `f` over the points with
   `lo₁ + x ≡ r` and `lo₂ + y ≡ s (mod p)` (`residueCounts_apply`), the residues represented in `[0, p)`.
3. **The hypotheses.** `P` is nonempty and consists of primes; `W` is `window P = 1 + Σ_{p ∈ P} (p − 1)`; `S` is
   `degreeSum`; `2 ≤ L ≤ S(⌊(W − 1)/(L − 1)⌋)` is `hL` and `hsize`, with the floor as natural-number division.
4. **The conclusions.** Determination is `residueCounts_determine`: equal residue counts imply equal functions.
   Recovery is `reconstruct`: a rational matrix `R`, accepted by the exact check `leftInverseCheck` (`R · A = 1` for the
   count matrix `A`), with `R · residueCounts … f = f` for every `f`.

## Documented deviations

- **Running time.** The theorem's last sentence, polynomial-time recovery by exact elimination, is not formalized.
  Lean proves that a checked rational left inverse exists and recovers every function.
- **The corollary.** The prime-window corollary is not a Lean theorem as stated. Lean has its window-size form: for
  every nonempty set of primes whose window `W` is large enough, the computable side `⌊⌊√⌊√W⌋⌋³/24⌋` is admissible
  (`reconstruct_at_side`), and it lies between `W^{3/4}/(16^{3/4}·48)` and `W^{3/4}` (`side_bounds`). With the window of
  the primes in `(P/2, P]`, of order `P²/log P`, this gives the corollary's order of side; that last combination is
  not formalized.

## Class

No circuits: rational-valued functions on a known integer box, a finite set of primes, and exact rational linear
algebra.
