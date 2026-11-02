# Integer threshold masks (`lem:maskpoly`)

[Mapping index](README.md) · a result of independent interest · no published premise

The identity `[X ≤ τ] = Σ_{a=0}^{D} c_a·C(X, a)` for `0 ≤ X ≤ D`, with integer Newton coefficients, is proved in
[Proof/Quartic/Mask/Polynomial.lean](../Proof/Quartic/Mask/Polynomial.lean) (namespace `NearQuarticWires.Mask`);
`NearQuarticWires.Reusable.threshold_eq_newton_sum` ([Reusable.lean](../Proof/Quartic/Reusable.lean)) states it with the
coefficients written out. [Check.lean](../Check.lean) prints its axioms and fails unless they are the standard three.

<!-- files -->
**Files.** The line numbers below are of these files:

- [`paper/paper.tex`](../paper/paper.tex), SHA-256 `32c365c3c97134031d57cc7fe42432513408376fadb04ada31f3a9205b38070e`
- [`Proof/Quartic/Mask/Polynomial.lean`](../Proof/Quartic/Mask/Polynomial.lean), SHA-256 `84db4e89c6ff1cadb738b652c50abce0a13c7e46b06004a8909f1bd09aaf5b2a`
- [`Proof/Quartic/Reusable.lean`](../Proof/Quartic/Reusable.lean), SHA-256 `e034f81728b0327aa706a74dfee447e1e4d75f48a96c33ec066d76a7dbcc2937`
<!-- /files -->

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>

<!-- paper file=paper/paper.tex label=lem:maskpoly -->
<b>paper/paper.tex, lines 1173–1202</b> ([paper/paper.tex](../paper/paper.tex#L1173-L1202))

<pre>
\begin{lemma}[Integer threshold masks]\label{lem:maskpoly}
For nonnegative integers \(\tau,D\), put
\[
 c_a=\sum_{i=0}^{\min(a,\tau)}(-1)^{a-i}\binom ai\in\Z
 \quad(0\le a\le D).
\]
Then \(|c_a|\le2^a\), and for every integer \(0\le X\le D\),
\[
 \ind[X\le\tau]=\sum_{a=0}^{D}c_a\binom Xa.
\]
Equivalently, for Boolean variables \(y_1,\ldots,y_G\),
\(P_{\tau,D}(y)=\sum_{a=0}^{D}c_a e_a(y)\) is a multilinear integer polynomial of degree at most \(D\), each coefficient has magnitude at most \(2^D\), and
\[
 P_{\tau,D}(y)=\ind\Bigl[\sum_i y_i\le\tau\Bigr]
 \quad\text{whenever }\sum_i y_i\le D.
\]
The same identity holds modulo every integer. Writing \(X=\sum_i y_i\), if \(s\in\{0,1\}\), then \(sP_{\tau,D}(y)=s\ind[X\le\tau]\) whenever \(X\le D\) or \(s=0\).

For the circuit mask, take \(D=\Xmax\), set
\(b_{j,i}=\Delta_{j,i}^2\), an integer polynomial of degree at most two
in the four atoms of \(T_{j,i}\). Define the integer polynomial
\[
 \Mpoly(z,u,v)=\smask(u,v)\sum_{a=0}^{\Xmax}c_a\,e_a\bigl((b_{j,i}(z,u,v))_{(j,i)\in\cS}\bigr),
\]
where \(e_a\) is the elementary symmetric polynomial of degree \(a\).
Then \(\Mpoly(z,u,v)=\mask(z,u,v)\) whenever \(X(z,u,v)\le\Xmax\) or
\(\smask(u,v)=0\). Its degree in the atoms is at most \(2\Xmax\), and
with separate atom variables for each bottom gate, after multilinearization its coefficients have \(O(\Xmax+\lambda_n)\)
bits.
\end{lemma}
</pre>
<!-- /paper -->

</td><td>

<!-- lean NearQuarticWires.Mask.cutoff -->
[Proof/Quartic/Mask/Polynomial.lean, lines 15–16](../Proof/Quartic/Mask/Polynomial.lean#L15-L16)

<pre title="Proof/Quartic/Mask/Polynomial.lean, lines 15–16">
/-- Paper `lem:maskpoly`: the integer cutoff function used by Newton interpolation. -/
def cutoff (τ x : ℕ) : ℤ := if x ≤ τ then 1 else 0
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Mask.newtonCoeff -->
[Proof/Quartic/Mask/Polynomial.lean, lines 18–19](../Proof/Quartic/Mask/Polynomial.lean#L18-L19)

<pre title="Proof/Quartic/Mask/Polynomial.lean, lines 18–19">
/-- Paper `lem:maskpoly`: the `a`th integer forward difference at zero. -/
def newtonCoeff (τ a : ℕ) : ℤ := ((fwdDiff (1 : ℕ))^[a] (cutoff τ)) 0
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Mask.newtonCoeff_eq_sum_min -->
[Proof/Quartic/Mask/Polynomial.lean, lines 73–95](../Proof/Quartic/Mask/Polynomial.lean#L73-L95)

<pre title="Proof/Quartic/Mask/Polynomial.lean, lines 73–95">
/-- Paper `lem:maskpoly`: the displayed explicit coefficient
with its exact upper index `min(a,τ)`. -/
theorem newtonCoeff_eq_sum_min (τ a : ℕ) :
    newtonCoeff τ a = ∑ i ∈ Finset.range (min a τ + 1),
      (-1 : ℤ) ^ (a - i) * (a.choose i : ℤ) := by
  rw [newtonCoeff_eq_sum]
  have hs : (∑ i ∈ Finset.range (min a τ + 1),
      (-1 : ℤ) ^ (a - i) * (a.choose i : ℤ) * cutoff τ i) =
      ∑ i ∈ Finset.range (a + 1),
        (-1 : ℤ) ^ (a - i) * (a.choose i : ℤ) * cutoff τ i := by
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (min_le_left _ _)))
    intro i hi hnot
    have hiτ : τ &lt; i := by
      simp only [Finset.mem_range] at hi hnot
      omega
    simp [cutoff, Nat.not_le.mpr hiτ]
  rw [← hs]
  apply Finset.sum_congr rfl
  intro i hi
  have hiτ : i ≤ τ := by
    simp only [Finset.mem_range] at hi
    omega
  simp [cutoff, hiτ]
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Mask.newtonCoeff_abs_le -->
[Proof/Quartic/Mask/Polynomial.lean, lines 97–109](../Proof/Quartic/Mask/Polynomial.lean#L97-L109)

<pre title="Proof/Quartic/Mask/Polynomial.lean, lines 97–109">
/-- Paper `lem:maskpoly`: each Newton coefficient has absolute
value at most `2^a`, an explicit integer coefficient-height bound. -/
theorem newtonCoeff_abs_le (τ a : ℕ) : |newtonCoeff τ a| ≤ (2 : ℤ) ^ a := by
  rw [newtonCoeff_eq_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range (a + 1),
        |(-1 : ℤ) ^ (a - i) * (a.choose i : ℤ) * cutoff τ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (a + 1), (a.choose i : ℤ) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : i ≤ τ &lt;;&gt; simp [cutoff, h, abs_mul, abs_pow]
    _ = (2 : ℤ) ^ a := by exact_mod_cast Nat.sum_range_choose a
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Mask.cutoff_eq_newton_sum_of_le -->
[Proof/Quartic/Mask/Polynomial.lean, lines 39–50](../Proof/Quartic/Mask/Polynomial.lean#L39-L50)

<pre title="Proof/Quartic/Mask/Polynomial.lean, lines 39–50">
/-- Paper `lem:maskpoly`: binomial vanishing permits the fixed
upper degree `Xmax`, rather than a population-dependent sum. -/
theorem cutoff_eq_newton_sum_of_le (τ X Xmax : ℕ) (hX : X ≤ Xmax) :
    cutoff τ X = ∑ a ∈ Finset.range (Xmax + 1),
      newtonCoeff τ a * (X.choose a : ℤ) := by
  rw [cutoff_eq_newton_sum]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hX))
  intro a ha hnot
  have hXa : X &lt; a := by
    simp only [Finset.mem_range] at hnot
    omega
  simp [Nat.choose_eq_zero_of_lt hXa]
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Mask.maskPoly_eq_mask -->
[Proof/Quartic/Mask/Polynomial.lean, lines 52–63](../Proof/Quartic/Mask/Polynomial.lean#L52-L63)

<pre title="Proof/Quartic/Mask/Polynomial.lean, lines 52–63">
/-- Paper `lem:maskpoly`: the concrete integer polynomial value
equals the scalar mask on every certified point, including structural zeros. -/
theorem maskPoly_eq_mask (structural : Bool) (τ Xmax X : ℕ)
    (h : X ≤ Xmax ∨ structural = false) :
    maskPolyEval structural τ Xmax X = mask structural τ X := by
  cases hs : structural with
  | false =&gt; simp [maskPolyEval, mask]
  | true =&gt;
    have hX : X ≤ Xmax := h.resolve_right (by simp [hs])
    simp only [maskPolyEval, ↓reduceIte, one_mul]
    rw [← cutoff_eq_newton_sum_of_le τ X Xmax hX]
    simp [cutoff, mask]
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Reusable.threshold_eq_newton_sum -->
[Proof/Quartic/Reusable.lean, lines 49–58](../Proof/Quartic/Reusable.lean#L49-L58)

<pre title="Proof/Quartic/Reusable.lean, lines 49–58">
/-- **Threshold masks are integer polynomials in the population.** For natural numbers `X ≤ X_max` and a threshold
`τ`, `[X ≤ τ] = Σ_{a=0}^{X_max} c_a(τ) · C(X, a)` with the integer coefficients
`c_a(τ) = Σ_{i=0}^{a} (−1)^{a−i} C(a, i) [i ≤ τ]`, which do not depend on `X` (`lem:maskpoly`). -/
theorem threshold_eq_newton_sum (τ X Xmax : ℕ) (hX : X ≤ Xmax) :
    (if X ≤ τ then (1 : ℤ) else 0) = ∑ a ∈ Finset.range (Xmax + 1),
      (∑ i ∈ Finset.range (a + 1), (-1 : ℤ) ^ (a - i) * (a.choose i : ℤ) * (if i ≤ τ then 1 else 0)) *
        (X.choose a : ℤ) := by
  have h := Mask.cutoff_eq_newton_sum_of_le τ X Xmax hX
  simp only [Mask.newtonCoeff_eq_sum] at h
  simpa only [Mask.cutoff] using h
</pre>
<!-- /lean -->

</td></tr>
</table>

## What to check

1. **The coefficients.** The paper's `c_a = Σ_{i=0}^{min(a,τ)} (−1)^{a−i} C(a, i)` is `newtonCoeff τ a`, the `a`-th
   forward difference at `0` of the cutoff `x ↦ [x ≤ τ]`; `newtonCoeff_eq_sum_min` proves the paper's formula and
   `newtonCoeff_abs_le` the bound `|c_a| ≤ 2^a`.
2. **The identity.** `cutoff_eq_newton_sum_of_le` is `[X ≤ τ] = Σ_{a=0}^{D} c_a·C(X, a)` for `X ≤ D` (`D = Xmax`), over
   `ℤ`; reduction modulo any integer preserves it.
3. **The structural factor.** `maskPoly_eq_mask` is the last sentence of the first paragraph: `s·P_{τ,D} = s·[X ≤ τ]`
   whenever `X ≤ D` or `s = 0`.

## Documented deviations

- **Boolean variables.** The paper's multilinear form `P_{τ,D}(y) = Σ_a c_a e_a(y)` is evaluated here through the
  population `X = Σ_i y_i`, since `e_a(y) = C(X, a)` on Boolean `y`; the circuit mask of the lemma's second paragraph
  is formalized in the same module (`indicatorPolynomial_eq_mask`) and is not printed here.

## Class

No circuits: integers, binomial coefficients and finite sums.
