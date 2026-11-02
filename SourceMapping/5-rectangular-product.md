# 5. Rectangular matrix product

[Mapping index](README.md) · derived field `rectangularProduct` · one published premise

The retained premise is `NearCubicGates.Published.Williams.RectangularProductLeaf` in
[Statement.lean](../Statement.lean). One deterministic multitape machine, its tapes, constants C,e and onset N₀
are chosen before the dimensions and matrices. For N ≥ N₀ and natural m = N^(1/10), it multiplies an N×m zero-one
matrix by an m×N zero-one matrix over the integers in O(N² poly(log N)) steps. Restricting to N = k^10 gives an
unbounded range of integral dimensions and avoids a rounding convention for N^(1/10).

Source: R. Williams, *Nonuniform ACC Circuit Lower Bounds*, J. ACM 61(1), Article 2 (2014),
[doi:10.1145/2559903](https://doi.org/10.1145/2559903), Corollary 4.4 (p.2:17), restated as Corollary C.2 (p.2:29).
Appendix C (p.2:26) explicitly discusses a multitape implementation. Pinned PDF SHA-256:
`78d7c472224906600e31369914d4210d875af894b92903c362c3c1cf680b021c`.

The source fixes no alphabet, tape layout or binary matrix codec. The retained model permits a general finite
alphabet, finite control and local unit head moves on one-sided tapes. Its **single combined input word** is A
row by row, a separator, then B row by row. Output entries are binary digits followed by separators. These are
explicit representation conventions, not a claim that Williams specifies two input tapes. Base-two logarithms
are also a convention: changing a fixed base changes the existential time constant.

[`Williams.Final.williams14_of_leaf`](../SourceAdapters/Williams/Final.lean) proves
`Williams14_Corollary4_4` in the target bit-multitape model. Its loader, finite-alphabet simulation and output
conversion are proved constructions. They supply the two input tapes, dimension header and fixed-width
output expected by the lower-bound proof. The natural-number sum of zero-one products is the integer matrix
product, and every entry is at most k ≤ N, so ⌊log₂ N⌋+1 bits suffice. The adapter raises the onset to at least 2;
no correctness claim below that onset is required.

The current [paper](../paper/near-cubic-gates-v3.tex) label is `imp:batch`. Check uniformity of the single source machine,
the onset, perfect-tenth-power specialization, arithmetic over integers and the source/target encoding
distinction. The binary simulation is a proved adapter conclusion, not another hypothesis.

## Published sources beside the retained Lean statements

The tables repeat selected mathematical declarations for direct comparison. Source quotations and explicitly marked mathematical or scan transcriptions carry their exact source versions and locators. The complete generated Lean declaration closure is retained below.

<!-- source-table williams -->
<h3>Williams: rectangular integer matrix product</h3>
<p>Corollary 4.4 is the published statement. Corollary C.2 repeats it after the implementation discussion.</p>
<p>The source does not define a tape alphabet, transition-table encoding, matrix byte codec, or a rounding convention for N^{.1}. These remain explicit transcription conventions, not additional quotations attributed to the paper.</p>
<p>The source definition of poly and its explicit multitape implementation statements are quoted below. The Lean existential constants C and e instantiate that asymptotic convention.</p>
<p>The display N^{.1} is transcribed as printed; the Lean natural dimension m satisfies (m : Real) = N^(1/10). Because m is a natural number with (m : ℝ) = N^(1/10), the premise speaks only about perfect tenth powers N = k^10; this restricts (weakens) the printed statement, and the adapter `williams14_of_leaf` instantiates exactly N = k^10, m = k.</p>
<table>
<tr><th>Published source (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<p><b>Corollary 4.4</b></p>
<p>Published JACM 61(1), Article 2, January 2014, DOI 10.1145/2559903; Corollary 4.4; printed p. 2:17; PDF p. 17. Pinned PDF SHA-256 <code>78d7c472224906600e31369914d4210d875af894b92903c362c3c1cf680b021c</code>.</p>
<p><i>Transcribed from the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. The source words and punctuation are retained.</i></p>

<pre>
For all sufficiently large \(N\), two 0-1 matrices of dimensions \(N\times N^{.1}\) and \(N^{.1}\times N\) can be multiplied over the integers in \(O(N^2\cdot\operatorname{poly}(\log N))\) time.
</pre>
</td><td>
<p>Retained premise field <code>NearCubicGates.Close.PublishedInputs.williams_rectangularProductLeaf</code>: <a href="../Statement.lean#L1830">Statement.lean, line 1830</a></p>

<pre>
  williams_rectangularProductLeaf : NearCubicGates.Published.Williams.RectangularProductLeaf
</pre>

<!-- lean NearCubicGates.Published.Williams.RectangularProductLeaf -->
[Statement.lean, lines 1797–1815](../Statement.lean#L1797-L1815)

<pre title="Statement.lean, lines 1797–1815">
/-- **Williams, JACM 2014, Corollary 4.4 (printed p. 2:17) = Corollary C.2 (printed p. 2:29), verbatim:**
"For all sufficiently large N, two 0-1 matrices of dimensions N × N^{.1} and N^{.1} × N can be multiplied over the
integers in O(N² · poly(log N)) time."
**Machine model (Appendix C, printed p. 2:26, verbatim):** "here we verify using standard ideas that Coppersmith's
algorithm can indeed be implemented to run (even on a multitape TM) in O(N² · poly(log N)) time, on matrices over
any field of poly(N) elements." **Uniformity (§4, printed p. 2:16, verbatim):** "Coppersmith's algorithm is
explicit, in that it can be executed on typical machine model (even a multitape TM) in O(N² · poly(log N)) time".

Read as: one multitape machine, constants `C`, `e` and an onset `N₀`, such that for every `N ≥ N₀` and every
natural `m` equal to `N^{.1}`, on every pair of 0-1 matrices of dimensions `N × m` and `m × N` the machine halts
within `C · N² · (log₂ N)^e` steps with their integer product on its output tape (conventions in the header). -/
def RectangularProductLeaf : Prop :=
  ∃ (M : MultitapeTM) (inputTape outputTape : Fin M.tapes) (C e N₀ : ℕ),
    ∀ (N m : ℕ), N₀ ≤ N → (m : ℝ) = (N : ℝ) ^ (1 / 10 : ℝ) →
    ∀ (A : Fin N → Fin m → Bool) (B : Fin m → Fin N → Bool),
      ∃ (t : ℕ) (c : M.Configuration),
        M.run t (M.initial inputTape (inputWord A B)) = some c ∧ M.step c = none ∧
        (t : ℝ) ≤ (C : ℝ) * (N : ℝ) ^ 2 * Real.logb 2 (N : ℝ) ^ e ∧
        c.contents outputTape = fun p =&gt; (outputWord (integerProduct A B)).getD p Symbol.blank
</pre>
<!-- /lean -->
<p>The retained premise is this integer 0-1 matrix multiplication statement, expressed with one fixed machine and fixed asymptotic constants.</p>
</td></tr>
<tr><td>
<p><b>Polynomial-time notation</b></p>
<p>Published JACM 61(1), Article 2, January 2014, DOI 10.1145/2559903; Notation paragraph; printed p. 2:6; PDF p. 6. Pinned PDF SHA-256 <code>78d7c472224906600e31369914d4210d875af894b92903c362c3c1cf680b021c</code>.</p>
<p><i>Transcribed from the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. The source words and punctuation are retained.</i></p>

<pre>
Inside of an algorithm description, the integer \(n\) refers to the length of the input to the algorithm. For a function \(f:\mathbb{N}\to\mathbb{N}\), we use \(\operatorname{poly}(f(n))\) to denote a growth rate of the form \(cf(n)^c\) for a constant \(c\).
</pre>
</td><td>

<!-- lean NearCubicGates.Published.Williams.RectangularProductLeaf -->
[Statement.lean, lines 1797–1815](../Statement.lean#L1797-L1815)

<pre title="Statement.lean, lines 1797–1815">
/-- **Williams, JACM 2014, Corollary 4.4 (printed p. 2:17) = Corollary C.2 (printed p. 2:29), verbatim:**
"For all sufficiently large N, two 0-1 matrices of dimensions N × N^{.1} and N^{.1} × N can be multiplied over the
integers in O(N² · poly(log N)) time."
**Machine model (Appendix C, printed p. 2:26, verbatim):** "here we verify using standard ideas that Coppersmith's
algorithm can indeed be implemented to run (even on a multitape TM) in O(N² · poly(log N)) time, on matrices over
any field of poly(N) elements." **Uniformity (§4, printed p. 2:16, verbatim):** "Coppersmith's algorithm is
explicit, in that it can be executed on typical machine model (even a multitape TM) in O(N² · poly(log N)) time".

Read as: one multitape machine, constants `C`, `e` and an onset `N₀`, such that for every `N ≥ N₀` and every
natural `m` equal to `N^{.1}`, on every pair of 0-1 matrices of dimensions `N × m` and `m × N` the machine halts
within `C · N² · (log₂ N)^e` steps with their integer product on its output tape (conventions in the header). -/
def RectangularProductLeaf : Prop :=
  ∃ (M : MultitapeTM) (inputTape outputTape : Fin M.tapes) (C e N₀ : ℕ),
    ∀ (N m : ℕ), N₀ ≤ N → (m : ℝ) = (N : ℝ) ^ (1 / 10 : ℝ) →
    ∀ (A : Fin N → Fin m → Bool) (B : Fin m → Fin N → Bool),
      ∃ (t : ℕ) (c : M.Configuration),
        M.run t (M.initial inputTape (inputWord A B)) = some c ∧ M.step c = none ∧
        (t : ℝ) ≤ (C : ℝ) * (N : ℝ) ^ 2 * Real.logb 2 (N : ℝ) ^ e ∧
        c.contents outputTape = fun p =&gt; (outputWord (integerProduct A B)).getD p Symbol.blank
</pre>
<!-- /lean -->
<p>The source uses asymptotic notation; the Lean premise exposes the constant, exponent, and onset explicitly. The logarithm base in Lean is a representation convention.</p>
</td></tr>
<tr><td>
<p><b>Multitape implementation</b></p>
<p>Published JACM 61(1), Article 2, January 2014, DOI 10.1145/2559903; Appendix C, paragraph after Lemma 6.1; printed p. 2:26; PDF p. 26. Pinned PDF SHA-256 <code>78d7c472224906600e31369914d4210d875af894b92903c362c3c1cf680b021c</code>.</p>
<p><i>Transcribed from the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. The source words and punctuation are retained.</i></p>

<pre>
Prima facie, it could be that Coppersmith’s algorithm is nonuniform, making it difficult to apply. For the sake of completeness, here we verify using standard ideas that Coppersmith’s algorithm can indeed be implemented to run (even on a multitape TM) in \(O(N^2\cdot\operatorname{poly}(\log N))\) time, on matrices over any field of \(\operatorname{poly}(N)\) elements. (As we work with 0-1 matrices \(A^{\prime\prime}\) and \(B^{\prime\prime}\) in our application, it suffices for us to work over a prime field of \(\operatorname{poly}(N)\) elements.)
</pre>
</td><td>

<!-- lean NearCubicGates.Published.Williams.MultitapeTM -->
[Statement.lean, lines 1722–1731](../Statement.lean#L1722-L1731)

<pre title="Statement.lean, lines 1722–1731">
/-- A deterministic multitape Turing machine: `tapes` one-sided tapes over `Symbol extraSymbols`, `states` control
states, a start state, and a partial transition function. A transition reads the scanned symbol of every tape and
gives the next state, the symbol written on every tape and the move of every head. -/
structure MultitapeTM where
  tapes : ℕ
  extraSymbols : ℕ
  states : ℕ
  start : Fin states
  transition : Fin states → (Fin tapes → Symbol extraSymbols) →
    Option (Fin states × (Fin tapes → Symbol extraSymbols) × (Fin tapes → Move))
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.Williams.MultitapeTM.step -->
[Statement.lean, lines 1751–1756](../Statement.lean#L1751-L1756)

<pre title="Statement.lean, lines 1751–1756">
/-- One step; `none` when no transition applies (the machine has halted). -/
def step (c : M.Configuration) : Option M.Configuration :=
  (M.transition c.state c.scanned).map fun a =&gt;
    { state := a.1
      heads := fun i =&gt; (a.2.2 i).apply (c.heads i)
      contents := fun i =&gt; Function.update (c.contents i) (c.heads i) (a.2.1 i) }
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.Williams.MultitapeTM.run -->
[Statement.lean, lines 1758–1761](../Statement.lean#L1758-L1761)

<pre title="Statement.lean, lines 1758–1761">
/-- `M.run t c = some c'`: from `c`, the machine makes exactly `t` steps and is then in `c'`. -/
def run : ℕ → M.Configuration → Option M.Configuration
  | 0, c =&gt; some c
  | t + 1, c =&gt; (M.step c).bind (run t)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.Williams.MultitapeTM.initial -->
[Statement.lean, lines 1763–1768](../Statement.lean#L1763-L1768)

<pre title="Statement.lean, lines 1763–1768">
/-- The initial configuration on `input` written on tape `inputTape`: start state, every head on cell `0`, every
other cell blank. -/
def initial (inputTape : Fin M.tapes) (input : List (Symbol M.extraSymbols)) : M.Configuration where
  state := M.start
  heads := fun _ =&gt; 0
  contents := fun i p =&gt; if i = inputTape then input.getD p Symbol.blank else Symbol.blank
</pre>
<!-- /lean -->
<p>Williams supplies the explicit multitape implementation assertion. The concrete finite alphabet, one-sided tapes, transition semantics, and input/output layout are the transcription conventions documented in Statement.lean, not source definitions supplied by Appendix C.</p>
</td></tr>
<tr><td>
<p><b>Corollary C.2</b></p>
<p>Published JACM 61(1), Article 2, January 2014, DOI 10.1145/2559903; Corollary C.2; printed p. 2:29; PDF p. 29. Pinned PDF SHA-256 <code>78d7c472224906600e31369914d4210d875af894b92903c362c3c1cf680b021c</code>.</p>
<p><i>Transcribed from the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. The source words and punctuation are retained.</i></p>

<pre>
For all sufficiently large \(N\), two 0-1 matrices of dimensions \(N\times N^{.1}\) and \(N^{.1}\times N\) can be multiplied over the integers in \(O(N^2\cdot\operatorname{poly}(\log N))\) time.
</pre>
</td><td>

<!-- lean NearCubicGates.Published.Williams.integerProduct -->
[Statement.lean, lines 1778–1781](../Statement.lean#L1778-L1781)

<pre title="Statement.lean, lines 1778–1781">
/-- "multiplied over the integers": `(A·B)(i,j) = Σ_l A(i,l)·B(l,j)` with the 0-1 entries read as the integers `0`,
`1`. All terms are nonnegative, so the value is a natural number. -/
def integerProduct {n m p : ℕ} (A : Fin n → Fin m → Bool) (B : Fin m → Fin p → Bool) : Fin n → Fin p → ℕ :=
  fun i j =&gt; ∑ l, (if A i l then 1 else 0) * (if B l j then 1 else 0)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.Williams.RectangularProductLeaf -->
[Statement.lean, lines 1797–1815](../Statement.lean#L1797-L1815)

<pre title="Statement.lean, lines 1797–1815">
/-- **Williams, JACM 2014, Corollary 4.4 (printed p. 2:17) = Corollary C.2 (printed p. 2:29), verbatim:**
"For all sufficiently large N, two 0-1 matrices of dimensions N × N^{.1} and N^{.1} × N can be multiplied over the
integers in O(N² · poly(log N)) time."
**Machine model (Appendix C, printed p. 2:26, verbatim):** "here we verify using standard ideas that Coppersmith's
algorithm can indeed be implemented to run (even on a multitape TM) in O(N² · poly(log N)) time, on matrices over
any field of poly(N) elements." **Uniformity (§4, printed p. 2:16, verbatim):** "Coppersmith's algorithm is
explicit, in that it can be executed on typical machine model (even a multitape TM) in O(N² · poly(log N)) time".

Read as: one multitape machine, constants `C`, `e` and an onset `N₀`, such that for every `N ≥ N₀` and every
natural `m` equal to `N^{.1}`, on every pair of 0-1 matrices of dimensions `N × m` and `m × N` the machine halts
within `C · N² · (log₂ N)^e` steps with their integer product on its output tape (conventions in the header). -/
def RectangularProductLeaf : Prop :=
  ∃ (M : MultitapeTM) (inputTape outputTape : Fin M.tapes) (C e N₀ : ℕ),
    ∀ (N m : ℕ), N₀ ≤ N → (m : ℝ) = (N : ℝ) ^ (1 / 10 : ℝ) →
    ∀ (A : Fin N → Fin m → Bool) (B : Fin m → Fin N → Bool),
      ∃ (t : ℕ) (c : M.Configuration),
        M.run t (M.initial inputTape (inputWord A B)) = some c ∧ M.step c = none ∧
        (t : ℝ) ≤ (C : ℝ) * (N : ℝ) ^ 2 * Real.logb 2 (N : ℝ) ^ e ∧
        c.contents outputTape = fun p =&gt; (outputWord (integerProduct A B)).getD p Symbol.blank
</pre>
<!-- /lean -->
<p>This repeats Corollary 4.4 after the implementation discussion. integerProduct is ordinary integer multiplication of zero-one matrices; rowMajor, inputWord, numberWord and outputWord fix the otherwise-unspecified representation.</p>
</td></tr>
</table>
<!-- /source-table -->

## Complete Lean declaration closure

Every declaration of [Statement.lean](../Statement.lean) that the published statement of this page uses and that the
[main page](main-theorem.md) or an earlier input page does not already print, verbatim. `check.py` re-renders this
block and checks that the closure of the release statement is printed in full on the main page and the input
pages.

<!-- statement -->
[Statement.lean, lines 1692–1697](../Statement.lean#L1692-L1697)

<pre title="Statement.lean, lines 1692–1697">
/-- The move of one head in one step. -/
inductive Move where
  | left
  | stay
  | right
deriving DecidableEq
</pre>

[Statement.lean, lines 1699–1703](../Statement.lean#L1699-L1703)

<pre title="Statement.lean, lines 1699–1703">
/-- Head positions on a one-sided tape: a left move on cell `0` stays on cell `0`. -/
def Move.apply : Move → ℕ → ℕ
  | .left, h =&gt; h - 1
  | .stay, h =&gt; h
  | .right, h =&gt; h + 1
</pre>

[Statement.lean, lines 1705–1707](../Statement.lean#L1705-L1707)

<pre title="Statement.lean, lines 1705–1707">
/-- A finite tape alphabet: `0` is the blank, `1` and `2` are the digits `0` and `1`, `3` is the separator, and the
`extra` further symbols are work symbols. -/
abbrev Symbol (extra : ℕ) := Fin (extra + 4)
</pre>

[Statement.lean, lines 1711–1712](../Statement.lean#L1711-L1712)

<pre title="Statement.lean, lines 1711–1712">
/-- The blank. -/
def blank {extra : ℕ} : Symbol extra := 0
</pre>

[Statement.lean, lines 1714–1715](../Statement.lean#L1714-L1715)

<pre title="Statement.lean, lines 1714–1715">
/-- The digit symbol of a bit. -/
def digit {extra : ℕ} (b : Bool) : Symbol extra := if b then 2 else 1
</pre>

[Statement.lean, lines 1717–1718](../Statement.lean#L1717-L1718)

<pre title="Statement.lean, lines 1717–1718">
/-- The separator. -/
def separator {extra : ℕ} : Symbol extra := 3
</pre>

[Statement.lean, lines 1722–1731](../Statement.lean#L1722-L1731)

<pre title="Statement.lean, lines 1722–1731">
/-- A deterministic multitape Turing machine: `tapes` one-sided tapes over `Symbol extraSymbols`, `states` control
states, a start state, and a partial transition function. A transition reads the scanned symbol of every tape and
gives the next state, the symbol written on every tape and the move of every head. -/
structure MultitapeTM where
  tapes : ℕ
  extraSymbols : ℕ
  states : ℕ
  start : Fin states
  transition : Fin states → (Fin tapes → Symbol extraSymbols) →
    Option (Fin states × (Fin tapes → Symbol extraSymbols) × (Fin tapes → Move))
</pre>

[Statement.lean, lines 1737–1741](../Statement.lean#L1737-L1741)

<pre title="Statement.lean, lines 1737–1741">
/-- A configuration: control state, head positions and tape contents (cell `p` of tape `i`). -/
structure Configuration where
  state : Fin M.states
  heads : Fin M.tapes → ℕ
  contents : Fin M.tapes → ℕ → Symbol M.extraSymbols
</pre>

[Statement.lean, lines 1745–1747](../Statement.lean#L1745-L1747)

<pre title="Statement.lean, lines 1745–1747">
/-- The symbols under the heads. -/
def Configuration.scanned (c : M.Configuration) : Fin M.tapes → Symbol M.extraSymbols :=
  fun i =&gt; c.contents i (c.heads i)
</pre>

[Statement.lean, lines 1751–1756](../Statement.lean#L1751-L1756)

<pre title="Statement.lean, lines 1751–1756">
/-- One step; `none` when no transition applies (the machine has halted). -/
def step (c : M.Configuration) : Option M.Configuration :=
  (M.transition c.state c.scanned).map fun a =&gt;
    { state := a.1
      heads := fun i =&gt; (a.2.2 i).apply (c.heads i)
      contents := fun i =&gt; Function.update (c.contents i) (c.heads i) (a.2.1 i) }
</pre>

[Statement.lean, lines 1758–1761](../Statement.lean#L1758-L1761)

<pre title="Statement.lean, lines 1758–1761">
/-- `M.run t c = some c'`: from `c`, the machine makes exactly `t` steps and is then in `c'`. -/
def run : ℕ → M.Configuration → Option M.Configuration
  | 0, c =&gt; some c
  | t + 1, c =&gt; (M.step c).bind (run t)
</pre>

[Statement.lean, lines 1763–1768](../Statement.lean#L1763-L1768)

<pre title="Statement.lean, lines 1763–1768">
/-- The initial configuration on `input` written on tape `inputTape`: start state, every head on cell `0`, every
other cell blank. -/
def initial (inputTape : Fin M.tapes) (input : List (Symbol M.extraSymbols)) : M.Configuration where
  state := M.start
  heads := fun _ =&gt; 0
  contents := fun i p =&gt; if i = inputTape then input.getD p Symbol.blank else Symbol.blank
</pre>

[Statement.lean, lines 1774–1776](../Statement.lean#L1774-L1776)

<pre title="Statement.lean, lines 1774–1776">
/-- The entries of a matrix row by row. -/
def rowMajor {α : Type} {n m : ℕ} (A : Fin n → Fin m → α) : List α :=
  (List.ofFn fun i =&gt; List.ofFn fun j =&gt; A i j).flatten
</pre>

[Statement.lean, lines 1778–1781](../Statement.lean#L1778-L1781)

<pre title="Statement.lean, lines 1778–1781">
/-- "multiplied over the integers": `(A·B)(i,j) = Σ_l A(i,l)·B(l,j)` with the 0-1 entries read as the integers `0`,
`1`. All terms are nonnegative, so the value is a natural number. -/
def integerProduct {n m p : ℕ} (A : Fin n → Fin m → Bool) (B : Fin m → Fin p → Bool) : Fin n → Fin p → ℕ :=
  fun i j =&gt; ∑ l, (if A i l then 1 else 0) * (if B l j then 1 else 0)
</pre>

[Statement.lean, lines 1783–1785](../Statement.lean#L1783-L1785)

<pre title="Statement.lean, lines 1783–1785">
/-- The input word: `A` row by row, a separator, `B` row by row. -/
def inputWord {extra n m p : ℕ} (A : Fin n → Fin m → Bool) (B : Fin m → Fin p → Bool) : List (Symbol extra) :=
  (rowMajor A).map Symbol.digit ++ Symbol.separator :: (rowMajor B).map Symbol.digit
</pre>

[Statement.lean, lines 1787–1789](../Statement.lean#L1787-L1789)

<pre title="Statement.lean, lines 1787–1789">
/-- One natural number: its base-2 digits (least significant first) and a separator. -/
def numberWord {extra : ℕ} (x : ℕ) : List (Symbol extra) :=
  (Nat.digits 2 x).map (fun d =&gt; Symbol.digit (decide (d = 1))) ++ [Symbol.separator]
</pre>

[Statement.lean, lines 1791–1793](../Statement.lean#L1791-L1793)

<pre title="Statement.lean, lines 1791–1793">
/-- The output word: the entries row by row, each as `numberWord`. -/
def outputWord {extra n p : ℕ} (P : Fin n → Fin p → ℕ) : List (Symbol extra) :=
  (rowMajor P).flatMap numberWord
</pre>

[Statement.lean, lines 1797–1815](../Statement.lean#L1797-L1815)

<pre title="Statement.lean, lines 1797–1815">
/-- **Williams, JACM 2014, Corollary 4.4 (printed p. 2:17) = Corollary C.2 (printed p. 2:29), verbatim:**
"For all sufficiently large N, two 0-1 matrices of dimensions N × N^{.1} and N^{.1} × N can be multiplied over the
integers in O(N² · poly(log N)) time."
**Machine model (Appendix C, printed p. 2:26, verbatim):** "here we verify using standard ideas that Coppersmith's
algorithm can indeed be implemented to run (even on a multitape TM) in O(N² · poly(log N)) time, on matrices over
any field of poly(N) elements." **Uniformity (§4, printed p. 2:16, verbatim):** "Coppersmith's algorithm is
explicit, in that it can be executed on typical machine model (even a multitape TM) in O(N² · poly(log N)) time".

Read as: one multitape machine, constants `C`, `e` and an onset `N₀`, such that for every `N ≥ N₀` and every
natural `m` equal to `N^{.1}`, on every pair of 0-1 matrices of dimensions `N × m` and `m × N` the machine halts
within `C · N² · (log₂ N)^e` steps with their integer product on its output tape (conventions in the header). -/
def RectangularProductLeaf : Prop :=
  ∃ (M : MultitapeTM) (inputTape outputTape : Fin M.tapes) (C e N₀ : ℕ),
    ∀ (N m : ℕ), N₀ ≤ N → (m : ℝ) = (N : ℝ) ^ (1 / 10 : ℝ) →
    ∀ (A : Fin N → Fin m → Bool) (B : Fin m → Fin N → Bool),
      ∃ (t : ℕ) (c : M.Configuration),
        M.run t (M.initial inputTape (inputWord A B)) = some c ∧ M.step c = none ∧
        (t : ℝ) ≤ (C : ℝ) * (N : ℝ) ^ 2 * Real.logb 2 (N : ℝ) ^ e ∧
        c.contents outputTape = fun p =&gt; (outputWord (integerProduct A B)).getD p Symbol.blank
</pre>
<!-- /statement -->
