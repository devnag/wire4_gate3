# 8. Hardness amplification from STV list decoding

[Mapping index](README.md) · derived field `amplification` · one published premise

[`Amplification.field8`](../SourceAdapters/Amplification/Field8.lean) proves
`NearCubicGates.Close.CLW20_Lemma3_9_Multitape` from
`NearCubicGates.Published.STV.Theorem29` alone. The intermediate statement is the full-range amplification
interface credited to CLW20 Lemma 3.9; that lemma is not itself a retained premise.

Source: M. Sudan, L. Trevisan and S. Vadhan, *Pseudorandom Generators without the XOR Lemma*, J. Comput. System
Sci. 62(2):236–266 (2001). Theorem 29 and Definition 20 were checked in the journal-version preprint (pp.17 and
13), PDF SHA-256 `6155baab46b3204122e9f2f801a70f891b9333f34cf396b1047809973ce53cf7`, and against
[ECCC TR98-074, revision 2](https://eccc.weizmann.ac.il/report/1998/074/), SHA-256
`87ccd011e2e0d55929decddd29caaf4b4c89659dee9c93760a8e29d950d59865`.

## The retained premise

The fields are binary polynomial-basis fields F₂[X]/(q), with q monic irreducible of degree t. The relevant
polynomials in m variables have **total** degree at most d. If ε > c√(d/|F|), the premise supplies a list of at
most L/ε randomized oracle machines. The absolute constants precede all parameters and the oracle; one list is
chosen before the polynomial to be recovered. Every degree-bounded polynomial agreeing with the oracle on at
least an ε fraction of points is computed by some member of that same list.

“Computes” means probability at least 3/4 **at each input point**, not agreement on 3/4 of the points. Every
machine halts on every random string within the stated polynomial budget. Its finite transition-table size and
coin count also have polynomial bounds, so a machine cannot hard-wire an arbitrarily large polynomial. Queries and field elements use explicit bit representations.

At d=0 the proviso is ε>0. The printed proof uses conditions such as ε≥256/|F| (Claim 37 and Lemma 39) and
|F|≥2(d+1) (Theorem 32). For d≥1 in the nontrivial range 0<ε≤1, these follow after choosing the absolute
constant c sufficiently large. If ε>1 there is no agreeing polynomial and the empty list suffices. At d=0,
at most 1/ε distinct constants can agree with the oracle on an ε fraction of points, and each is computed by a
constant-output machine. This extends the retained conclusion to d=0 without adding a source hypothesis or
assuming a procedure that finds the list.

The publication gives a randomized reconstruction procedure. The retained statement takes only the existence of
a successful output list, which follows from positive success probability; it does not assume a uniform
deterministic procedure for choosing that successful list. Binary-field representation and ordinary oracle-machine
conventions are documented in [Statement.lean](../Statement.lean).

## The proved consequence

For every time-constructible size bound S, the derived amplifier maps each n-bit function f to a function g of
O(n) bits. If f has no circuit of size S(n), then circuits of size S(n)^(1/c) agree with g on less than a
1/2 + S(n)^(−1/c) fraction of inputs. Its truth table is constructed in 2^O(n) time. Circuit size counts nodes,
including inputs and constants; the full range, including small and sublinear S, is part of the proved theorem.

The [reconstruction](../SourceAdapters/Amplification/Reconstruction.lean),
[truth-table construction](../SourceAdapters/Amplification/Construction.lean), finite exceptional cases and
[ordinary-to-TM2 time conversion](../SourceAdapters/Machine/OrdinaryToTM2.lean) are supplied proofs. The main
lower-bound proof's later polynomial-clock specialization does not replace the full-range theorem by an assumption.
The current [paper](../paper/near-cubic-gates-v3.tex) labels are `imp:ae-amplification` and `app:sources`.

## Published sources beside the retained Lean statements

The tables repeat selected mathematical declarations for direct comparison. Source quotations and explicitly marked mathematical or scan transcriptions carry their exact source versions and locators. The complete generated Lean declaration closure is retained below.

<!-- source-table stv -->
<h3>Sudan–Trevisan–Vadhan: polynomial reconstruction</h3>
<p>All source quotations on this page are transcribed from the scanned ECCC TR98-074 revision 2 PDF, SHA256 87ccd011e2e0d55929decddd29caaf4b4c89659dee9c93760a8e29d950d59865.</p>
<p>Printed page 17 is physical PDF page 18; printed page 13 is physical PDF page 14. The extra physical page is the unnumbered first page. Physical PDF page 17 contains printed page 16, not Theorem 29.</p>
<p>The statement specializes the source field F to polynomial-basis binary fields F₂[X]/(q). The concrete bit tapes, finite transition tables, fieldElt, and query layout are explicit Lean representation conventions; the source paragraphs below do not prescribe those codecs.</p>
<p>The source reconstructs an implicit representation and defines computation pointwise with success probability at least 3/4. The retained premise asks only for the existence of a successful output list, with description, coin, and runtime bounds, rather than adding a deterministic list-construction hypothesis.</p>
<p>The d=0 extension and parameter specializations remain in the existing explanatory prose; they are not inserted into a source quotation.</p>
<table>
<tr><th>Published source (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<p><b>Theorem 29</b></p>
<p>ECCC TR98-074 revision 2, May 18, 2000; Theorem 29, §4.3; printed p. 17; PDF p. 18. Pinned PDF SHA-256 <code>87ccd011e2e0d55929decddd29caaf4b4c89659dee9c93760a8e29d950d59865</code>.</p>
<p><i>Transcribed from the scanned page of ECCC TR98-074 revision 2. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. The source words and punctuation are retained. Physical PDF page numbers include the unnumbered first page.</i></p>

<pre>
There exists a constant \(c\) such that the reconstruction problem above can be solved in time \(\operatorname{poly}(m,d,\log|F|,1/\varepsilon)\), provided \(\varepsilon&gt;c\sqrt{d/|F|}\). Furthermore, the reconstruction algorithm produces a list of at most \(l=O(1/\varepsilon)\) oracle machines, each with running time at most \(\operatorname{poly}(m,d,\log|F|,1/\varepsilon)\).
</pre>
</td><td>
<p>Retained premise field <code>NearCubicGates.Close.PublishedInputs.stv_theorem29</code>: <a href="../Statement.lean#L1833">Statement.lean, line 1833</a></p>

<pre>
  stv_theorem29 : NearCubicGates.Published.STV.Theorem29
</pre>

<!-- lean NearCubicGates.Published.STV.Theorem29 -->
[Statement.lean, lines 1561–1587](../Statement.lean#L1561-L1587)

<pre title="Statement.lean, lines 1561–1587">
/-- **STV Theorem 29** (§4.3, p. 17):

"Recall that we wish to solve the following problem:
Given: An oracle f : F^m → F and parameters d ∈ ℕ and ε ∈ ℝ.
Goal: Reconstruct (an implicit representation for) every polynomial of total degree at most d that has
ε-agreement with the function f. Specifically, construct randomized oracle machines M1, …, Ml such that for every
polynomial p : F^m → F of degree d that has (relative) agreement ε with f, there exists j ∈ [l] such that M_j^f
computes p. …
Theorem 29 There exists a constant c such that the reconstruction problem above can be solved in time
poly(m, d, log|F|, 1/ε), provided ε &gt; c√(d/|F|). Furthermore, the reconstruction algorithm produces a list of at
most l = O(1/ε) oracle machines, each with running time at most poly(m, d, log|F|, 1/ε)."

Stated for `F = 𝔽₂[X]/(q)` (`|F| = 2^t`), as the existence of the reconstruction's output list (see the record
above). -/
def Theorem29 : Prop :=
  ∃ (c L K : ℝ) (e : ℕ), 0 &lt; c ∧
    ∀ (t : ℕ) (q : (ZMod 2)[X]), q.Monic → Irreducible q → q.natDegree = t →
    ∀ (m d : ℕ) (ε : ℝ), c * Real.sqrt ((d : ℝ) / 2 ^ t) &lt; ε →
    ∀ f : (Fin m → Fin t → Bool) → Fin t → Bool,
    ∃ Ms : List OracleMachine,
      (Ms.length : ℝ) ≤ L / ε ∧
      (∀ M ∈ Ms,
        ((M.stateCount * 2 ^ M.tapeCount : ℕ) : ℝ) ≤ K * ((m : ℝ) + d + t + 1 / ε) ^ e ∧
        (M.randomBits : ℝ) ≤ K * ((m : ℝ) + d + t + 1 / ε) ^ e ∧
        M.HaltsWithin f (K * ((m : ℝ) + d + t + 1 / ε) ^ e)) ∧
      ∀ P : MvPolynomial (Fin m) (AdjoinRoot q), P.totalDegree ≤ d → Agrees q f P ε →
        ∃ M ∈ Ms, M.Computes q f P
</pre>
<!-- /lean -->
<p>The reconstruction problem referred to by this statement is quoted next. The Lean premise exposes the absolute constants and specializes the field representation.</p>
</td></tr>
<tr><td>
<p><b>The reconstruction problem</b></p>
<p>ECCC TR98-074 revision 2, May 18, 2000; §4.3, problem immediately preceding Theorem 29; printed p. 17; PDF p. 18. Pinned PDF SHA-256 <code>87ccd011e2e0d55929decddd29caaf4b4c89659dee9c93760a8e29d950d59865</code>.</p>
<p><i>Transcribed from the scanned page of ECCC TR98-074 revision 2. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. The source words and punctuation are retained. Physical PDF page numbers include the unnumbered first page.</i></p>

<pre>
Recall that we wish to solve the following problem:
Given: An oracle \(f:F^m\to F\) and parameters \(d\in\mathbb{N}\) and \(\varepsilon\in\mathbb{R}\).
Goal: Reconstruct (an implicit representation for) every polynomial of total degree at most \(d\) that has \(\varepsilon\)-agreement with the function \(f\). Specifically, construct randomized oracle machines \(M_1,\ldots,M_l\) such that for every polynomial \(p:F^m\to F\) of degree \(d\) that has (relative) agreement \(\varepsilon\) with \(f\), there exists \(j\in[l]\) such that \(M_j^f\) computes \(p\).
</pre>
</td><td>

<!-- lean NearCubicGates.Published.STV.Theorem29 -->
[Statement.lean, lines 1561–1587](../Statement.lean#L1561-L1587)

<pre title="Statement.lean, lines 1561–1587">
/-- **STV Theorem 29** (§4.3, p. 17):

"Recall that we wish to solve the following problem:
Given: An oracle f : F^m → F and parameters d ∈ ℕ and ε ∈ ℝ.
Goal: Reconstruct (an implicit representation for) every polynomial of total degree at most d that has
ε-agreement with the function f. Specifically, construct randomized oracle machines M1, …, Ml such that for every
polynomial p : F^m → F of degree d that has (relative) agreement ε with f, there exists j ∈ [l] such that M_j^f
computes p. …
Theorem 29 There exists a constant c such that the reconstruction problem above can be solved in time
poly(m, d, log|F|, 1/ε), provided ε &gt; c√(d/|F|). Furthermore, the reconstruction algorithm produces a list of at
most l = O(1/ε) oracle machines, each with running time at most poly(m, d, log|F|, 1/ε)."

Stated for `F = 𝔽₂[X]/(q)` (`|F| = 2^t`), as the existence of the reconstruction's output list (see the record
above). -/
def Theorem29 : Prop :=
  ∃ (c L K : ℝ) (e : ℕ), 0 &lt; c ∧
    ∀ (t : ℕ) (q : (ZMod 2)[X]), q.Monic → Irreducible q → q.natDegree = t →
    ∀ (m d : ℕ) (ε : ℝ), c * Real.sqrt ((d : ℝ) / 2 ^ t) &lt; ε →
    ∀ f : (Fin m → Fin t → Bool) → Fin t → Bool,
    ∃ Ms : List OracleMachine,
      (Ms.length : ℝ) ≤ L / ε ∧
      (∀ M ∈ Ms,
        ((M.stateCount * 2 ^ M.tapeCount : ℕ) : ℝ) ≤ K * ((m : ℝ) + d + t + 1 / ε) ^ e ∧
        (M.randomBits : ℝ) ≤ K * ((m : ℝ) + d + t + 1 / ε) ^ e ∧
        M.HaltsWithin f (K * ((m : ℝ) + d + t + 1 / ε) ^ e)) ∧
      ∀ P : MvPolynomial (Fin m) (AdjoinRoot q), P.totalDegree ≤ d → Agrees q f P ε →
        ∃ M ∈ Ms, M.Computes q f P
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.STV.Agrees -->
[Statement.lean, lines 1556–1559](../Statement.lean#L1556-L1559)

<pre title="Statement.lean, lines 1556–1559">
/-- "p has (relative) agreement ε with f": `p(x) = f(x)` on at least an `ε` fraction of `F^m`. -/
def Agrees (q : (ZMod 2)[X]) {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool)
    (P : MvPolynomial (Fin m) (AdjoinRoot q)) (ε : ℝ) : Prop :=
  ε * 2 ^ (m * t) ≤ ({x : Fin m → Fin t → Bool | fieldElt q (f x) = evalAt q P x}.ncard : ℝ)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.STV.evalAt -->
[Statement.lean, lines 1463–1466](../Statement.lean#L1463-L1466)

<pre title="Statement.lean, lines 1463–1466">
/-- The value of `P` at the point of `F^m` denoted by the words `x`. -/
noncomputable def evalAt (q : (ZMod 2)[X]) {m t : ℕ} (P : MvPolynomial (Fin m) (AdjoinRoot q))
    (x : Fin m → Fin t → Bool) : AdjoinRoot q :=
  MvPolynomial.eval (fun i =&gt; fieldElt q (x i)) P
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.STV.fieldElt -->
[Statement.lean, lines 1459–1461](../Statement.lean#L1459-L1461)

<pre title="Statement.lean, lines 1459–1461">
/-- The element of `F = 𝔽₂[X]/(q)` denoted by a `t`-bit word (polynomial-basis representation). -/
noncomputable def fieldElt (q : (ZMod 2)[X]) {t : ℕ} (w : Fin t → Bool) : AdjoinRoot q :=
  AdjoinRoot.mk q (wordPoly w)
</pre>
<!-- /lean -->
<p>The source uses total degree and one common output list for every agreeing polynomial. The polynomial-basis quotient and its bit-word representation are the declared specialization.</p>
</td></tr>
<tr><td>
<p><b>Which running times are bounded</b></p>
<p>ECCC TR98-074 revision 2, May 18, 2000; §4.3, paragraph immediately preceding Theorem 29; printed p. 17; PDF p. 18. Pinned PDF SHA-256 <code>87ccd011e2e0d55929decddd29caaf4b4c89659dee9c93760a8e29d950d59865</code>.</p>
<p><i>Transcribed from the scanned page of ECCC TR98-074 revision 2. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. The source words and punctuation are retained. Physical PDF page numbers include the unnumbered first page.</i></p>

<pre>
We will be interested in the running time of the “reconstruction procedure”, i.e., the time taken to generate the machines \(M_1,\ldots,M_l\), as well as the running times of the machines \(M_1,\ldots,M_l\).
</pre>
</td><td>

<!-- lean NearCubicGates.Published.STV.Theorem29 -->
[Statement.lean, lines 1561–1587](../Statement.lean#L1561-L1587)

<pre title="Statement.lean, lines 1561–1587">
/-- **STV Theorem 29** (§4.3, p. 17):

"Recall that we wish to solve the following problem:
Given: An oracle f : F^m → F and parameters d ∈ ℕ and ε ∈ ℝ.
Goal: Reconstruct (an implicit representation for) every polynomial of total degree at most d that has
ε-agreement with the function f. Specifically, construct randomized oracle machines M1, …, Ml such that for every
polynomial p : F^m → F of degree d that has (relative) agreement ε with f, there exists j ∈ [l] such that M_j^f
computes p. …
Theorem 29 There exists a constant c such that the reconstruction problem above can be solved in time
poly(m, d, log|F|, 1/ε), provided ε &gt; c√(d/|F|). Furthermore, the reconstruction algorithm produces a list of at
most l = O(1/ε) oracle machines, each with running time at most poly(m, d, log|F|, 1/ε)."

Stated for `F = 𝔽₂[X]/(q)` (`|F| = 2^t`), as the existence of the reconstruction's output list (see the record
above). -/
def Theorem29 : Prop :=
  ∃ (c L K : ℝ) (e : ℕ), 0 &lt; c ∧
    ∀ (t : ℕ) (q : (ZMod 2)[X]), q.Monic → Irreducible q → q.natDegree = t →
    ∀ (m d : ℕ) (ε : ℝ), c * Real.sqrt ((d : ℝ) / 2 ^ t) &lt; ε →
    ∀ f : (Fin m → Fin t → Bool) → Fin t → Bool,
    ∃ Ms : List OracleMachine,
      (Ms.length : ℝ) ≤ L / ε ∧
      (∀ M ∈ Ms,
        ((M.stateCount * 2 ^ M.tapeCount : ℕ) : ℝ) ≤ K * ((m : ℝ) + d + t + 1 / ε) ^ e ∧
        (M.randomBits : ℝ) ≤ K * ((m : ℝ) + d + t + 1 / ε) ^ e ∧
        M.HaltsWithin f (K * ((m : ℝ) + d + t + 1 / ε) ^ e)) ∧
      ∀ P : MvPolynomial (Fin m) (AdjoinRoot q), P.totalDegree ≤ d → Agrees q f P ε →
        ∃ M ∈ Ms, M.Computes q f P
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.STV.OracleMachine.HaltsWithin -->
[Statement.lean, lines 1548–1552](../Statement.lean#L1548-L1552)

<pre title="Statement.lean, lines 1548–1552">
/-- "running time at most T": with oracle `f`, on every point and every coin string, the machine halts within
`T` transitions. -/
def HaltsWithin {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool) (T : ℝ) : Prop :=
  ∀ (x : Fin m → Fin t → Bool) (r : Fin M.randomBits → Bool), ∃ fuel : ℕ, (fuel : ℝ) ≤ T ∧
    (M.oracleRun (fieldOracle f) fuel (M.initial (pointWord x) (List.ofFn r))).isSome
</pre>
<!-- /lean -->
<p>The source bounds both the reconstruction procedure and the machines it outputs. The retained list-existence premise states the resulting finite-description, coin, and runtime bounds explicitly.</p>
</td></tr>
<tr><td>
<p><b>Definition 20: computation and agreement</b></p>
<p>ECCC TR98-074 revision 2, May 18, 2000; Definition 20, §4.1; printed p. 13; PDF p. 14. Pinned PDF SHA-256 <code>87ccd011e2e0d55929decddd29caaf4b4c89659dee9c93760a8e29d950d59865</code>.</p>
<p><i>Transcribed from the scanned page of ECCC TR98-074 revision 2. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. The source words and punctuation are retained. Physical PDF page numbers include the unnumbered first page.</i></p>

<pre>
A randomized procedure \(A\) is said to compute a function \(f:X\to Y\) at a point \(x\in X\) if \(\Pr[A(x)=f(x)]\ge3/4\), where the probability is taken over the internal coin tosses of \(A\). We say that \(A\) has agreement \(\alpha\in[0,1]\) with \(f\) if \(A\) computes \(f\) on an \(\alpha\) fraction of the inputs in \(X\). We say that \(A\) computes \(f\) if it has agreement \(1\) with \(f\). A randomized procedure \(A\) is said to solve a search problem \(S\), if on input \(x\), \(\Pr[A(x)\in S(x)]\ge3/4\).
</pre>
</td><td>

<!-- lean NearCubicGates.Published.STV.OracleMachine.Computes -->
[Statement.lean, lines 1538–1546](../Statement.lean#L1538-L1546)

<pre title="Statement.lean, lines 1538–1546">
/-- STV Definition 20 (§4.1, p. 13): "A randomized procedure A is said to compute a function f : X → Y at a
point x ∈ X if Pr[A(x) = f(x)] ≥ 3/4, where the probability is taken over the internal coin tosses of A. … We
say that A computes f if it has agreement 1 with f."

`M^f` computes the polynomial function `P` (at every point, over the uniform coins). -/
def Computes (q : (ZMod 2)[X]) {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool)
    (P : MvPolynomial (Fin m) (AdjoinRoot q)) : Prop :=
  ∀ x : Fin m → Fin t → Bool,
    3 * 2 ^ M.randomBits ≤ 4 * {r : Fin M.randomBits → Bool | M.OutputsValue q f x r (evalAt q P x)}.ncard
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.STV.OracleMachine.OutputsValue -->
[Statement.lean, lines 1532–1536](../Statement.lean#L1532-L1536)

<pre title="Statement.lean, lines 1532–1536">
/-- On point `x` with coins `r` and oracle `f`, the machine halts with an output denoting `v`. -/
def OutputsValue (q : (ZMod 2)[X]) {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool)
    (x : Fin m → Fin t → Bool) (r : Fin M.randomBits → Bool) (v : AdjoinRoot q) : Prop :=
  ∃ fuel c, M.oracleRun (fieldOracle f) fuel (M.initial (pointWord x) (List.ofFn r)) = some c ∧
    fieldElt q (M.outputWord t c) = v
</pre>
<!-- /lean -->
<p>Computes is pointwise success probability at least 3/4, not correctness on only three quarters of the inputs. The final sentence gives the source meaning of solving the randomized reconstruction search problem.</p>
</td></tr>
<tr><td>
<p><b>Implicit words and oracle-machine notation</b></p>
<p>ECCC TR98-074 revision 2, May 18, 2000; §4.1, second computational-requirements bullet, sentences beginning “Thus”; printed p. 13; PDF p. 14. Pinned PDF SHA-256 <code>87ccd011e2e0d55929decddd29caaf4b4c89659dee9c93760a8e29d950d59865</code>.</p>
<p><i>Transcribed from the scanned page of ECCC TR98-074 revision 2. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. The source words and punctuation are retained. Physical PDF page numbers include the unnumbered first page.</i></p>

<pre>
Thus we will assume we have oracle access to the received word \(r\) (the input). We will also output the codewords implicitly, by programs that compute the function represented by the codeword. These programs will be allowed to make oracle calls to the received word \(r\). Thus both our decoding algorithm and their output programs are best thought of as oracle-machines. We will use the notation \(M^{\mathcal{O}}(x)\) to denote the computation of an oracle-machine \(M\) on input \(x\) with access to an oracle \(\mathcal{O}\). When asking for efficient list-decoding, we will expect that the decoding algorithm, as well as its output programs are all efficient.
</pre>
<p>ECCC TR98-074 revision 2, May 18, 2000; §4.1, third computational-requirements bullet; printed p. 13; PDF p. 14. Pinned PDF SHA-256 <code>87ccd011e2e0d55929decddd29caaf4b4c89659dee9c93760a8e29d950d59865</code>.</p>
<p><i>Transcribed from the scanned page of ECCC TR98-074 revision 2. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. The source words and punctuation are retained. Physical PDF page numbers include the unnumbered first page.</i></p>

<pre>
Finally, we will allow our decoding algorithms, as well as their output programs, to be randomized. Below we define what it means for randomized algorithms to approximately compute functions, and to solve search problems.
</pre>
</td><td>

<!-- lean NearCubicGates.Published.STV.OracleMachine -->
[Statement.lean, lines 1482–1490](../Statement.lean#L1482-L1490)

<pre title="Statement.lean, lines 1482–1490">
/-- A randomized oracle machine: a multitape bit machine with five designated tapes — `0` input, `1` coins,
`2` query, `3` answer, `4` output — query states `asks`, and `randomBits` coins. -/
structure OracleMachine where
  tapeCount : ℕ
  stateCount : ℕ
  fiveTapes : 5 ≤ tapeCount
  machine : Machine tapeCount stateCount
  asks : Fin stateCount → Bool
  randomBits : ℕ
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.STV.OracleMachine.oracleStep -->
[Statement.lean, lines 1500–1509](../Statement.lean#L1500-L1509)

<pre title="Statement.lean, lines 1500–1509">
/-- One transition with oracle `O`: the machine's own step; if it enters a query state, the answer to the
query tape replaces the answer tape, whose head returns to cell `0`. -/
def oracleStep (O : List Bool → List Bool) (c : Configuration M.tapeCount M.stateCount) :
    Option (Configuration M.tapeCount M.stateCount) :=
  (step M.machine c).map fun c' =&gt;
    if M.asks c'.control then
      { control := c'.control
        heads := Function.update c'.heads M.answerTape 0
        tapes := Function.update c'.tapes M.answerTape (O (c'.tapes M.queryTape)) }
    else c'
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.STV.OracleMachine.oracleRun -->
[Statement.lean, lines 1511–1520](../Statement.lean#L1511-L1520)

<pre title="Statement.lean, lines 1511–1520">
/-- Run with oracle `O` for at most `fuel` transitions; `some` the halting configuration. -/
def oracleRun (O : List Bool → List Bool) :
    ℕ → Configuration M.tapeCount M.stateCount → Option (Configuration M.tapeCount M.stateCount)
  | 0, c =&gt; if M.machine.halted c.control then some c else none
  | fuel + 1, c =&gt;
      if M.machine.halted c.control then some c
      else
        match M.oracleStep O c with
        | none =&gt; none
        | some c' =&gt; oracleRun O fuel c'
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.STV.fieldOracle -->
[Statement.lean, lines 1476–1478](../Statement.lean#L1476-L1478)

<pre title="Statement.lean, lines 1476–1478">
/-- The oracle `f : F^m → F` as an answer map on query-tape contents. -/
def fieldOracle {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool) : List Bool → List Bool :=
  fun tape =&gt; List.ofFn (f (queryPoint m t tape))
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.STV.queryPoint -->
[Statement.lean, lines 1472–1474](../Statement.lean#L1472-L1474)

<pre title="Statement.lean, lines 1472–1474">
/-- The point named by the first `m·t` cells of a tape (cells beyond the written part read as `false`). -/
def queryPoint (m t : ℕ) (tape : List Bool) : Fin m → Fin t → Bool :=
  fun i j =&gt; readTapeBit tape (i.val * t + j.val)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.STV.pointWord -->
[Statement.lean, lines 1468–1470](../Statement.lean#L1468-L1470)

<pre title="Statement.lean, lines 1468–1470">
/-- A point of `F^m` written on a tape: the `m` words of `t` bits, one after the other. -/
def pointWord {m t : ℕ} (x : Fin m → Fin t → Bool) : List Bool :=
  (List.ofFn fun i : Fin m =&gt; List.ofFn (x i)).flatten
</pre>
<!-- /lean -->
<p>The source defines the oracle computation interface. The five distinguished tapes and their bit layout are the concrete machine-model conventions used to transcribe it.</p>
</td></tr>
<tr><td>
<p><b>Relative Hamming distance</b></p>
<p>ECCC TR98-074 revision 2, May 18, 2000; §4.1, opening paragraph of printed page 13; printed p. 13; PDF p. 14. Pinned PDF SHA-256 <code>87ccd011e2e0d55929decddd29caaf4b4c89659dee9c93760a8e29d950d59865</code>.</p>
<p><i>Transcribed from the scanned page of ECCC TR98-074 revision 2. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. The source words and punctuation are retained. Physical PDF page numbers include the unnumbered first page.</i></p>

<pre>
For codes to be of use to us, we will need that the codewords are sufficiently “far” from each other. So we define the Hamming distance between two vectors \(x,y\in[q]^n\) to be the number of coordinates i such that \(x(i)\ne y(i)\). (Notice we are already using the functional notation!) The relative Hamming distance, denoted \(\Delta(x,y)\), is \(\Pr_{i\in[n]}[x(i)\ne y(i)]\).
</pre>
</td><td>

<!-- lean NearCubicGates.Published.STV.Agrees -->
[Statement.lean, lines 1556–1559](../Statement.lean#L1556-L1559)

<pre title="Statement.lean, lines 1556–1559">
/-- "p has (relative) agreement ε with f": `p(x) = f(x)` on at least an `ε` fraction of `F^m`. -/
def Agrees (q : (ZMod 2)[X]) {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool)
    (P : MvPolynomial (Fin m) (AdjoinRoot q)) (ε : ℝ) : Prop :=
  ε * 2 ^ (m * t) ≤ ({x : Fin m → Fin t → Bool | fieldElt q (f x) = evalAt q P x}.ncard : ℝ)
</pre>
<!-- /lean -->
<p>Agrees uses the fraction of points at which the two function values coincide. Its inequality is the usual agreement-at-least-ε convention; the surrounding source problem and its uses concern agreeing polynomials, not a specified tape encoding.</p>
</td></tr>
</table>
<!-- /source-table -->

## Complete Lean declaration closure

Every declaration of [Statement.lean](../Statement.lean) that the published statement of this page uses and that the
[main page](main-theorem.md) or an earlier input page does not already print, verbatim. `check.py` re-renders this
block and checks that the closure of the release statement is printed in full on the main page and the input
pages.

<!-- statement -->
[Statement.lean, lines 1455–1457](../Statement.lean#L1455-L1457)

<pre title="Statement.lean, lines 1455–1457">
/-- The polynomial `Σ_{w_i = 1} X^i` of a `t`-bit word. -/
noncomputable def wordPoly {t : ℕ} (w : Fin t → Bool) : (ZMod 2)[X] :=
  ∑ i : Fin t, if w i then (X : (ZMod 2)[X]) ^ (i : ℕ) else 0
</pre>

[Statement.lean, lines 1459–1461](../Statement.lean#L1459-L1461)

<pre title="Statement.lean, lines 1459–1461">
/-- The element of `F = 𝔽₂[X]/(q)` denoted by a `t`-bit word (polynomial-basis representation). -/
noncomputable def fieldElt (q : (ZMod 2)[X]) {t : ℕ} (w : Fin t → Bool) : AdjoinRoot q :=
  AdjoinRoot.mk q (wordPoly w)
</pre>

[Statement.lean, lines 1463–1466](../Statement.lean#L1463-L1466)

<pre title="Statement.lean, lines 1463–1466">
/-- The value of `P` at the point of `F^m` denoted by the words `x`. -/
noncomputable def evalAt (q : (ZMod 2)[X]) {m t : ℕ} (P : MvPolynomial (Fin m) (AdjoinRoot q))
    (x : Fin m → Fin t → Bool) : AdjoinRoot q :=
  MvPolynomial.eval (fun i =&gt; fieldElt q (x i)) P
</pre>

[Statement.lean, lines 1468–1470](../Statement.lean#L1468-L1470)

<pre title="Statement.lean, lines 1468–1470">
/-- A point of `F^m` written on a tape: the `m` words of `t` bits, one after the other. -/
def pointWord {m t : ℕ} (x : Fin m → Fin t → Bool) : List Bool :=
  (List.ofFn fun i : Fin m =&gt; List.ofFn (x i)).flatten
</pre>

[Statement.lean, lines 1472–1474](../Statement.lean#L1472-L1474)

<pre title="Statement.lean, lines 1472–1474">
/-- The point named by the first `m·t` cells of a tape (cells beyond the written part read as `false`). -/
def queryPoint (m t : ℕ) (tape : List Bool) : Fin m → Fin t → Bool :=
  fun i j =&gt; readTapeBit tape (i.val * t + j.val)
</pre>

[Statement.lean, lines 1476–1478](../Statement.lean#L1476-L1478)

<pre title="Statement.lean, lines 1476–1478">
/-- The oracle `f : F^m → F` as an answer map on query-tape contents. -/
def fieldOracle {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool) : List Bool → List Bool :=
  fun tape =&gt; List.ofFn (f (queryPoint m t tape))
</pre>

[Statement.lean, lines 1482–1490](../Statement.lean#L1482-L1490)

<pre title="Statement.lean, lines 1482–1490">
/-- A randomized oracle machine: a multitape bit machine with five designated tapes — `0` input, `1` coins,
`2` query, `3` answer, `4` output — query states `asks`, and `randomBits` coins. -/
structure OracleMachine where
  tapeCount : ℕ
  stateCount : ℕ
  fiveTapes : 5 ≤ tapeCount
  machine : Machine tapeCount stateCount
  asks : Fin stateCount → Bool
  randomBits : ℕ
</pre>

[Statement.lean, line 1496](../Statement.lean#L1496)

<pre title="Statement.lean, line 1496">
def queryTape : Fin M.tapeCount := ⟨2, by have := M.fiveTapes; omega⟩
</pre>

[Statement.lean, line 1497](../Statement.lean#L1497)

<pre title="Statement.lean, line 1497">
def answerTape : Fin M.tapeCount := ⟨3, by have := M.fiveTapes; omega⟩
</pre>

[Statement.lean, line 1498](../Statement.lean#L1498)

<pre title="Statement.lean, line 1498">
def outputTape : Fin M.tapeCount := ⟨4, by have := M.fiveTapes; omega⟩
</pre>

[Statement.lean, lines 1500–1509](../Statement.lean#L1500-L1509)

<pre title="Statement.lean, lines 1500–1509">
/-- One transition with oracle `O`: the machine's own step; if it enters a query state, the answer to the
query tape replaces the answer tape, whose head returns to cell `0`. -/
def oracleStep (O : List Bool → List Bool) (c : Configuration M.tapeCount M.stateCount) :
    Option (Configuration M.tapeCount M.stateCount) :=
  (step M.machine c).map fun c' =&gt;
    if M.asks c'.control then
      { control := c'.control
        heads := Function.update c'.heads M.answerTape 0
        tapes := Function.update c'.tapes M.answerTape (O (c'.tapes M.queryTape)) }
    else c'
</pre>

[Statement.lean, lines 1511–1520](../Statement.lean#L1511-L1520)

<pre title="Statement.lean, lines 1511–1520">
/-- Run with oracle `O` for at most `fuel` transitions; `some` the halting configuration. -/
def oracleRun (O : List Bool → List Bool) :
    ℕ → Configuration M.tapeCount M.stateCount → Option (Configuration M.tapeCount M.stateCount)
  | 0, c =&gt; if M.machine.halted c.control then some c else none
  | fuel + 1, c =&gt;
      if M.machine.halted c.control then some c
      else
        match M.oracleStep O c with
        | none =&gt; none
        | some c' =&gt; oracleRun O fuel c'
</pre>

[Statement.lean, lines 1522–1526](../Statement.lean#L1522-L1526)

<pre title="Statement.lean, lines 1522–1526">
/-- The start: the input word on tape `0`, the coins on tape `1`, every other tape empty, heads at `0`. -/
def initial (input coins : List Bool) : Configuration M.tapeCount M.stateCount where
  control := M.machine.start
  heads := fun _ =&gt; 0
  tapes := fun i =&gt; if i.val = 0 then input else if i.val = 1 then coins else []
</pre>

[Statement.lean, lines 1528–1530](../Statement.lean#L1528-L1530)

<pre title="Statement.lean, lines 1528–1530">
/-- The `t`-bit output word: the first `t` cells of the output tape. -/
def outputWord (t : ℕ) (c : Configuration M.tapeCount M.stateCount) : Fin t → Bool :=
  fun j =&gt; readTapeBit (c.tapes M.outputTape) j.val
</pre>

[Statement.lean, lines 1532–1536](../Statement.lean#L1532-L1536)

<pre title="Statement.lean, lines 1532–1536">
/-- On point `x` with coins `r` and oracle `f`, the machine halts with an output denoting `v`. -/
def OutputsValue (q : (ZMod 2)[X]) {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool)
    (x : Fin m → Fin t → Bool) (r : Fin M.randomBits → Bool) (v : AdjoinRoot q) : Prop :=
  ∃ fuel c, M.oracleRun (fieldOracle f) fuel (M.initial (pointWord x) (List.ofFn r)) = some c ∧
    fieldElt q (M.outputWord t c) = v
</pre>

[Statement.lean, lines 1538–1546](../Statement.lean#L1538-L1546)

<pre title="Statement.lean, lines 1538–1546">
/-- STV Definition 20 (§4.1, p. 13): "A randomized procedure A is said to compute a function f : X → Y at a
point x ∈ X if Pr[A(x) = f(x)] ≥ 3/4, where the probability is taken over the internal coin tosses of A. … We
say that A computes f if it has agreement 1 with f."

`M^f` computes the polynomial function `P` (at every point, over the uniform coins). -/
def Computes (q : (ZMod 2)[X]) {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool)
    (P : MvPolynomial (Fin m) (AdjoinRoot q)) : Prop :=
  ∀ x : Fin m → Fin t → Bool,
    3 * 2 ^ M.randomBits ≤ 4 * {r : Fin M.randomBits → Bool | M.OutputsValue q f x r (evalAt q P x)}.ncard
</pre>

[Statement.lean, lines 1548–1552](../Statement.lean#L1548-L1552)

<pre title="Statement.lean, lines 1548–1552">
/-- "running time at most T": with oracle `f`, on every point and every coin string, the machine halts within
`T` transitions. -/
def HaltsWithin {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool) (T : ℝ) : Prop :=
  ∀ (x : Fin m → Fin t → Bool) (r : Fin M.randomBits → Bool), ∃ fuel : ℕ, (fuel : ℝ) ≤ T ∧
    (M.oracleRun (fieldOracle f) fuel (M.initial (pointWord x) (List.ofFn r))).isSome
</pre>

[Statement.lean, lines 1556–1559](../Statement.lean#L1556-L1559)

<pre title="Statement.lean, lines 1556–1559">
/-- "p has (relative) agreement ε with f": `p(x) = f(x)` on at least an `ε` fraction of `F^m`. -/
def Agrees (q : (ZMod 2)[X]) {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool)
    (P : MvPolynomial (Fin m) (AdjoinRoot q)) (ε : ℝ) : Prop :=
  ε * 2 ^ (m * t) ≤ ({x : Fin m → Fin t → Bool | fieldElt q (f x) = evalAt q P x}.ncard : ℝ)
</pre>

[Statement.lean, lines 1561–1587](../Statement.lean#L1561-L1587)

<pre title="Statement.lean, lines 1561–1587">
/-- **STV Theorem 29** (§4.3, p. 17):

"Recall that we wish to solve the following problem:
Given: An oracle f : F^m → F and parameters d ∈ ℕ and ε ∈ ℝ.
Goal: Reconstruct (an implicit representation for) every polynomial of total degree at most d that has
ε-agreement with the function f. Specifically, construct randomized oracle machines M1, …, Ml such that for every
polynomial p : F^m → F of degree d that has (relative) agreement ε with f, there exists j ∈ [l] such that M_j^f
computes p. …
Theorem 29 There exists a constant c such that the reconstruction problem above can be solved in time
poly(m, d, log|F|, 1/ε), provided ε &gt; c√(d/|F|). Furthermore, the reconstruction algorithm produces a list of at
most l = O(1/ε) oracle machines, each with running time at most poly(m, d, log|F|, 1/ε)."

Stated for `F = 𝔽₂[X]/(q)` (`|F| = 2^t`), as the existence of the reconstruction's output list (see the record
above). -/
def Theorem29 : Prop :=
  ∃ (c L K : ℝ) (e : ℕ), 0 &lt; c ∧
    ∀ (t : ℕ) (q : (ZMod 2)[X]), q.Monic → Irreducible q → q.natDegree = t →
    ∀ (m d : ℕ) (ε : ℝ), c * Real.sqrt ((d : ℝ) / 2 ^ t) &lt; ε →
    ∀ f : (Fin m → Fin t → Bool) → Fin t → Bool,
    ∃ Ms : List OracleMachine,
      (Ms.length : ℝ) ≤ L / ε ∧
      (∀ M ∈ Ms,
        ((M.stateCount * 2 ^ M.tapeCount : ℕ) : ℝ) ≤ K * ((m : ℝ) + d + t + 1 / ε) ^ e ∧
        (M.randomBits : ℝ) ≤ K * ((m : ℝ) + d + t + 1 / ε) ^ e ∧
        M.HaltsWithin f (K * ((m : ℝ) + d + t + 1 / ε) ^ e)) ∧
      ∀ P : MvPolynomial (Fin m) (AdjoinRoot q), P.totalDegree ≤ d → Agrees q f P ε →
        ∃ M ∈ Ms, M.Computes q f P
</pre>
<!-- /statement -->
