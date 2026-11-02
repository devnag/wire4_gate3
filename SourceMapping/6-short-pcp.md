# 6. Short PCP with an ordinary circuit-construction machine

[Mapping index](README.md) · derived field `shortPCP` · two published premises

[`Assembly.Fixed.field6OrdinaryFixed`](../SourceAdapters/Assembly/Field6Fixed.lean) proves
`OrdinaryOracleCircuitPCP` from exactly `NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1_Fixed` and
`NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17`. Their source models are in
[Statement.lean](../Statement.lean). The target is described in
[`Assembly/OrdinaryField.lean`](../SourceAdapters/Assembly/OrdinaryField.lean); its construction algorithm is an
ordinary polynomial-time word function, not an assumed Mathlib TM2 constructor.

For each ordinary verifier V and time function T with n ≤ T(n), assuming V halts within T(n) on all inputs and
witnesses, the theorem supplies a uniform constructor. It reads x and the binary clock T(|x|), each framed, and
writes the exact oracle-circuit word. Its running time and circuit size are polynomial in |x|+log T(|x|).
The circuit has ℓ input bits and ℓ-bit oracle addresses, with 2^ℓ ≤ K T(n) logScale(T(n))^e.

If an accepting witness of length T(n) exists, some oracle makes the circuit false on every input. If no such
witness exists, every oracle makes it true on at least a 1−1/n fraction of inputs. These are the PCP's reject
circuits: their satisfying assignments are rejecting random strings. The assertions use n ≥ 1. The clock is
supplied as input; no unproved efficient algorithm for computing an arbitrary function T is assumed.

## Retained results and their domains

BCGT13 is E. Ben-Sasson, A. Chiesa, D. Genkin and E. Tromer, *On the Concrete Efficiency of
Probabilistically-Checkable Proofs*, [ECCC TR12-045, revision 3](https://eccc.weizmann.ac.il/report/2012/045/),
Theorem 11.1 (p.51), Definition 4.15, Equation (6) (p.53) and the specified RS/VRS verifiers. The pinned PDF has
SHA-256 `9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0`.

The retained statement is **the proof-established form of Theorem 11.1 at (η,κ₀,γ,μ) = (2,4,0,1)**,
`BCGT13_Theorem11_1_Fixed`. For κ = |B| it uses K(κ)=16κ^{log₂c}, with c the unchanged constant of Theorem 11.3:
RS rejects with probability at least δ/(1+K(κ)), and VRS at least δ/(2+K(κ)). The field, affine-subspace, completeness and remaining quantifiers are unchanged from the recorded printed
statement `BCGT13_Theorem11_1`, which states the degree ranges explicitly: 1 ≤ d < 2^κ for V_RS and
2^λ ≤ d < 2^κ for V_VRS. It is not a verbatim copy of the printed soundness bound.
The corrected reductions are described below.

[`Field6Fixed.lean`](../SourceAdapters/Assembly/Field6Fixed.lean) proves that the tuple satisfies Equation (6)
(`fixed_valid`) and has positive exponents log₂(6/5) and log₂(5/3) (`fixed_positive_exponents`). The generic
`soundTerm` and full `BCGT13_Theorem11_1` in [Statement.lean](../Statement.lean) retain the printed sum-form
statement for comparison; they are not release inputs. `bcgt13Fixed_of_theorem11_1` proves that this stronger
printed record implies the retained fixed bound. This is a proved weakening, not just substitution of a tuple.
The release assumes the bound established by the repaired source argument; it does not assume the printed
constant.

The BCGT premise supplies completeness and soundness of the named mathematical verifiers, not a running-time
bound or a RAM reduction. Its documented semantic choices follow Algorithm 12's VRS equation, the vanishing and
interpolation output specifications, least-significant-bit-first subspace indexing, and zero answers for absent
queries. The source's inconsistent pseudocode passages are identified in the retained statement. In particular,
no general numerical bound from Lemma C.1 is assumed; the needed bounds for the chosen tuple are proved.

The second premise is deterministic polynomial-time construction of an irreducible degree-f polynomial over F₂
from unary f ≥ 1, with its f+1 coefficients written constant-first. This is **Algorithm 17, FindIrrPoly**, on
p.124 of the same pinned BCGT source. It cites Shoup's FOCS 1988 Corollary 3.2. Algorithm 17 and Corollary 3.2
in the [technical-report version](https://minds.wisc.edu/server/api/core/bitstreams/e8a2f9a9-6216-42c3-8bc0-bba2fa6ca98b/content)
were checked directly: V. Shoup, *New Algorithms for Finding Irreducible Polynomials over Finite Fields*,
UW–Madison Computer Sciences Technical Report 763, April 1, 1988, §3 (printed p.8; PDF p.9). The corollary states:

> We can construct an irreducible polynomial over F of degree n deterministically in time polynomial in n and p.

Here F = GF(p); setting p = 2 gives polynomial time in the degree. The pinned report has SHA-256
`14c05b951140d2b8996ecdac6edac7aad4c2d3a9687247b16758a421b4fee4de`.
No claim about degree zero or primitive polynomials is imported.

## Proved construction

The [affine constraint model](../SourceAdapters/ACSP/Affine.lean) uses one assignment polynomial and genuine
field-affine neighbors aX+b; its [encoding](../SourceAdapters/ACSP/Encoding.lean) is defined separately. The [RAM-to-constraint assembly](../SourceAdapters/RAMACSP/Assembly.lean) proves its
completeness and soundness; the generator prints the compact instance with an ordinary program whose cost is proved. It does not
enumerate an exponentially large computation graph. The exact model and codecs are part of this proof.

The fixed-tuple recursion estimates are proved in
[`LemmaC1.lean`](../SourceAdapters/ShortPCP/LemmaC1.lean), by
`NearCubicGates.Adapters.ShortPCP.lemmaC1`: for κ≥1 at (2,4,0,1),
`randEq κ ≤ κ+3 log₂(2κ)` and `lengthEq κ ≤ 2^κ κ³`. The proof uses the actual recursions (27) and (28);
`LemmaC1.randEq_le_real` and `LemmaC1.lengthEq_le` give the two bounds. It does not assume the general numerical
claim of Lemma C.1.

For comparison, the parameter range printed for Lemma C.1 includes (2,3,1,1), which satisfies Equation (6).
At κ=8, recurrence (28) gives length 19456, whereas the displayed bound
`2^κ κ^{1+max{−γ+μ+1,γ}}` gives `2^8·8²=16384`. This comparison concerns the broader Equation (6) range:
its e₂ is zero, so it is outside the positive-exponent soundness domain retained by the release. The release
uses only the independently proved recursion bounds at (2,4,0,1).

The remaining stages are the single-run verifier and its
[`Time.singleRunTime`](../SourceAdapters/ShortPCP/TimeCells.lean), amplification and masks, the bounded
[computation-to-circuit compiler](../SourceAdapters/Compile/OraclePrintMain.lean), and the final ordinary
constructor in [`ShortPCP.OracleCircuitPCP`](../SourceAdapters/ShortPCP/Assembly.lean). These suppliers discharge
the implementation requirements of `field6OrdinaryFixed`; none of them is an assumption.

The current [paper](../paper/near-cubic-gates-v3.tex) labels are `imp:short-pcp`, `app:short-pcp-proof`,
`thm:short-pcp-ours`, `def:acsp` and `thm:embedding`. Murray–Williams' SIAM J. Comput. 2020 Section 5 supplies the
oracle-circuit formulation as mathematical context; it is not a retained premise. The paper's
`rem:bv14-printed` discusses the scope of the SAT-compression formulation. The release uses the bounded-verifier
formulation described above.

## Documented deviations

- **Fixed tuple and weakened soundness.** The release uses only (2,4,0,1), with the proof-established bound below.
  The full printed record quantifies over more tuples and has a stronger displayed soundness constant; it is not
  the retained premise.
- **Algorithm 21 (FindSubspPoly, p.126).** The printed recurrence `Z(x²) + Z(a)·Z(x)` does not compute the
  vanishing polynomial over an extension field; the transcription uses its stated output, `Z_S(x) = ∏_{s∈S}(x − s)`,
  whose recurrence is `Z(x)² + Z(a)·Z(x)`. Over `F₈` with basis `1, 2, 4` the printed recurrence gives `3` at a
  point of the subspace, the corrected one `0` (`Vacuity.BCGT13Printed.printed_recurrence_witness`,
  `corrected_recurrence_witness`, [`BCGT13Printed.lean`](../SourceAdapters/Vacuity/BCGT13Printed.lean)).
- **Algorithm 23 (SubspaceInterp).** The printed base case `(x − α_{j2^κ})·(x − α_{j2^κ+1})` is not an
  interpolation: over `ZMod 2` with the basis `[1]` and the values `0, 0` it takes the value `1` at the node `1`
  (`Vacuity.BCGT13Printed.printed_base_not_interpolation`), while the zero polynomial interpolates
  (`intended_zero_interpolates`). The transcription uses the stated output specification, an existential degree
  test on the values in GetEltWithIndex order ([Statement.lean](../Statement.lean), section 10, item 5).
- **The VRS equation (§12.3.5, p.84).** In its printed orientation, `p̃(α) = Z_H(α)·p(α)`, the verifier rejects
  honest proofs: over `F₈` an honest instance is accepted on `1` of `8` coin strings
  (`Vacuity.BCGT13Printed.swapped_honest_count`). The transcription follows Algorithm 12 step 2(g),
  `p(α) = Z_H(α)·p̃(α)`, under which the same instance is accepted on all `8` (`actual_honest_count`).

- **The soundness reductions (the proof of Theorem 11.3 (stated on p.53), p.62; Lemma 11.10, pp.66–67; Corollaries 11.13 and 11.15, p.68).**
  Theorem 11.1 prints `(2^{η+1}+κ^{log c})/(1−2^{−η})`. The proof of Corollary 11.13 balances its cases with
  `a=(1−2^{−η})/(2^{η+1}κ^{log c})`, which yields the product `2^{η+1}κ^{log c}/(1−2^{−η})`.
  In Lemma 11.10, writing D=d_{κ,η}, the shifted polynomial `x^{D−d}P` can have degree up to `2D−d`.
  The resulting distance bound is `1−2^{1−η}`, rather than the printed `1−2^{−η}`. Correcting both steps gives
  `K=2^{2η}κ^{log c}/(2^{η−1}−1)`, hence `K=16κ^{log₂c}` at η=2. Lemma 11.14 gives RS rejection at least
  δ/(1+K), and Lemma 11.16 gives VRS rejection at least δ/(2+K).

  To see the constants, write Q=κ^{log₂c} and α=(2^{η−1}−1)/2^η. Corollary 11.4 gives rejection at least δ/Q
  for the equal-degree test, and the repaired Lemma 11.10 gives at least αδ/Q for the less-degree test.
  Lemma 11.12 then gives the minimum of `(1−τ)δ` and `ατδ/(2^η Q)`. With `K=2^η Q/α` and
  `τ=K/(1+K)`, both equal δ/(1+K); Lemma 11.14 gives the same uniform RS bound. Lemma 11.16 gives the minimum
  of `τδ/(1+K)` and `(1−τ)δ`; setting `τ=(1+K)/(2+K)` gives δ/(2+K). These calculations concern the
  nontrivial fractional-distance range 0≤δ≤1; the small exact-test cases satisfy the same weaker bounds.
  The retained far-form statement still quantifies over every real δ: δ≤0 is immediate, while δ>1 cannot
  satisfy its premise because the codes are nonempty. Its degree guards exclude an empty basis.

  On p.62, keep the error event jointly with the good-row event until substituting the nearest-row polynomial.
  On a good row that polynomial agrees with the bivariate candidate, so the joint error is bounded by the
  average nearest-row distance. This justifies the same subsequent estimate and leaves Theorem 11.3's c unchanged.

  The distance issue has a checked witness in
  [`BCGT13Case2Distance.lean`](../SourceAdapters/Vacuity/BCGT13Case2Distance.lean), namespace
  `NearCubicGates.Adapters.Vacuity.BCGT13Case2Distance`: `printed_case2_distance_counterexample` and
  `actual_distance`. Over the actual field of 16 elements, with κ=4, η=2 and d=0, a degree-three polynomial P
  has shifted table `x³P` at distance 10/16 from an actual RS codeword, below 3/4. This differs from the printed
  distance assertion; the witness does not address the conclusion of Corollary 11.13. A positive-degree control is proved in
  [`BCGT13Case2Positive.lean`](../SourceAdapters/Vacuity/BCGT13Case2Positive.lean), namespace
  `NearCubicGates.Adapters.Vacuity.BCGT13Case2Positive`: `positive_degree_distance_counterexample` and
  `actual_distance_positive` give distance 11/16<3/4 for d=1 and the shift `x²P`. The retained input uses the
  repaired argument above.

The finite checks for the three listing choices are in
[`BCGT13Printed.lean`](../SourceAdapters/Vacuity/BCGT13Printed.lean), under
`NearCubicGates.Adapters.Vacuity.BCGT13Printed`:

| Passage | Named checks |
|---|---|
| Algorithm 21 | `actual_product_witness`, `printed_recurrence_witness`, `corrected_recurrence_witness`, `printed_and_corrected_differ` |
| Algorithm 23 | `alg23_basis_valid`, `alg23_one_is_node`, `alg23_printed_base_wrong_value`, `printed_base_not_interpolation`, `intended_zero_interpolates` |
| VRS equation and the tested verifiers | `swapped_honest_count`, `actual_honest_count`, `tested_RS_is_actual`, `tested_VRS_is_actual` |

## Published sources beside the retained Lean statements

The tables repeat selected mathematical declarations for direct comparison. Source quotations and explicitly marked mathematical or scan transcriptions carry their exact source versions and locators. The complete generated Lean declaration closure is retained below.

<!-- source-table bcgt-fixed -->
<h3>BCGT13: the printed source and the proof-established fixed-tuple release premise</h3>
<p>The source column prints the published statements as printed, including the original soundness formula. The retained fixed-tuple bound and the recorded listing conventions are identified explicitly; they are not substituted into a purported verbatim quotation.</p>
<p>Mathematical typography is transcribed using Unicode and plain-text superscripts/subscripts, and every such quote is marked transcribed. The full source PDF identity and physical/printed locators are given for independent comparison.</p>
<p>The rows below also give the definitions and verifier listings that the fixed BCGT13 statement uses. Source listings are verbatim; transcription choices and proved adjustments are stated outside the quotations.</p>
<table>
<tr><th>Published source (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<p><b>Printed Theorem 11.1 beside the retained fixed-tuple premise</b></p>
<p>BCGT ECCC TR12-045 revision 3, December 28, 2012; Theorem 11.1, first display and its parameter introduction; printed p. 51; PDF p. 51. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Mathematical notation transcribed from the rendered page; superscripts/subscripts are written using ^ and _, fractions using parentheses, with typographic line wrapping normalized.</i></p>

<pre>
Theorem 11.1. The (strong) PCPP verifiers V_RS and V_VRS have respective soundness functions
s_RS(δ,n) ≥ (1/(1 + (2^(η+1) + κ^(log c))/(1−2^(−η)))) δ and
s_VRS(δ,n) ≥ (1/(2 + (2^(η+1) + κ^(log c))/(1−2^(−η)))) δ,
where n = 2^κ, (η,κ_0,γ,µ) are any integers satisfying
</pre>
</td><td>
<p>Retained premise field <code>NearCubicGates.Close.PublishedInputs.bcgt13_theorem11_1</code>: <a href="../Statement.lean#L1831">Statement.lean, line 1831</a></p>

<pre>
  bcgt13_theorem11_1 : NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1_Fixed
</pre>

<!-- lean NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1_Fixed -->
[Statement.lean, lines 1065–1087](../Statement.lean#L1065-L1087)

<pre title="Statement.lean, lines 1065–1087">
/-- **BCGT13 Theorem 11.1 at `(η, κ0, γ, μ) = (2, 4, 0, 1)`, with a weaker proof bound:** using
`1−2^{1−η}` for the distance in Lemma 11.10 and the product obtained from Corollary 11.13's τ algebra
(rather than the printed sum) gives `K(κ) = 16·κ^{log₂ c}`, RS denominator `1+K` and VRS denominator
`2+K` (ECCC rev. 3, pp.67–69).
The verifiers, constant `c`, completeness, degree ranges and all other quantifiers are unchanged, and
`bcgt13Fixed_of_theorem11_1` proves that the recorded printed statement implies this fixed release input. -/
def BCGT13_Theorem11_1_Fixed : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (ℓ : ℕ), Fintype.card F = 2 ^ ℓ →
  ∀ (B : List F) (O : F), IsBasis B O →
    -- V_RS on explicit input (I_ℓ, B_S, O_S, d), "d, positive integer indicating what “low-degree” means"
    -- (Algorithm 13 inputs, p.119; §12.3.4, p.82: "… and d is a positive integer")
    (∀ d : ℕ, 1 ≤ d → d &lt; 2 ^ B.length →
      (∀ p ∈ RS (span B O) d, ∃ π, ∀ r, (vRS Tuple.fixed B O d).accepts B O p π r = true) ∧
      ∀ (p : F → F) (π : Fin (vRS Tuple.fixed B O d).length → F) (δ : ℝ),
        (∀ q ∈ RS (span B O) d, δ ≤ fracDist (span B O) p q) →
        (vRS Tuple.fixed B O d).acceptProb B O p π ≤ 1 - δ / (1 + repairedSoundTerm B.length)) ∧
    -- V_VRS on explicit input (I_ℓ, B_S, O_S, B_H, O_H, d)
    (∀ (BH : List F) (OH : F), IsBasis BH OH → span BH OH ⊆ span B O →
     ∀ d : ℕ, 2 ^ BH.length ≤ d → d &lt; 2 ^ B.length →
      (∀ p ∈ VRS (span B O) (span BH OH) d, ∃ π, ∀ r, (vVRS Tuple.fixed B O BH OH d).accepts B O p π r = true) ∧
      ∀ (p : F → F) (π : Fin (vVRS Tuple.fixed B O BH OH d).length → F) (δ : ℝ),
        (∀ q ∈ VRS (span B O) (span BH OH) d, δ ≤ fracDist (span B O) p q) →
        (vVRS Tuple.fixed B O BH OH d).acceptProb B O p π ≤ 1 - δ / (2 + repairedSoundTerm B.length))
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.Tuple.fixed -->
[Statement.lean, lines 701–702](../Statement.lean#L701-L702)

<pre title="Statement.lean, lines 701–702">
/-- The tuple `(η, κ0, γ, μ) = (2, 4, 0, 1)`, the only one the release uses (`BCGT13_Theorem11_1_Fixed`). -/
def Tuple.fixed : Tuple := ⟨2, 4, 0, 1⟩
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.repairedSoundTerm -->
[Statement.lean, lines 678–682](../Statement.lean#L678-L682)

<pre title="Statement.lean, lines 678–682">
/-- The fixed-tuple soundness term established by the BCGT13 proof after correcting the distance in
Lemma 11.10 and the balancing algebra in Corollary 11.13 (ECCC rev. 3, pp.67–68):
`K(κ) = 16·κ^{log₂ c}` at `(η, κ0, γ, μ) = (2, 4, 0, 1)`. -/
noncomputable def repairedSoundTerm (κ : ℕ) : ℝ :=
  16 * (κ : ℝ) ^ Real.logb 2 (constC 2 4 0 1)
</pre>
<!-- /lean -->
<p>The source column is the original printed sum-form bound. The Lean field is the separately identified proof-established weakening at (2,4,0,1), with K(κ)=16κ^(log₂c); these are not claimed to be literal identical formulas. The derivation and witnesses above explain the retained bound.</p>
</td></tr>
<tr><td>
<p><b>Printed parameter conditions and the printed definition of c</b></p>
<p>BCGT ECCC TR12-045 revision 3, December 28, 2012; Theorem 11.1, all seven conditions and the definition of c; printed p. 51; PDF p. 51. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Mathematical notation transcribed from the rendered page; superscripts/subscripts are written using ^ and _, fractions using parentheses, with typographic line wrapping normalized.</i></p>
<p><b>Marked omissions:</b> The parenthetical alternative effective-c discussion after the displayed definition is omitted.</p>

<pre>
min{⌊(κ_0+1)/2⌋−γ, ⌈(κ_0+1)/2⌉+γ} ≥ 1
max{⌊(κ_0+1)/2⌋−γ+µ+1, ⌈(κ_0+1)/2⌉+γ} ≤ κ_0
min{⌊(κ_0+1)/2⌋−γ+µ+1, ⌈(κ_0+1)/2⌉+γ} ≥ η+1
κ_0 + (3+(−1)^(κ_0 mod 2))/2 &gt; ⌊(κ_0 + (3+(−1)^(κ_0 mod 2))/2)/2⌋−γ+µ+1,
κ_0 + (1+(−1)^(κ_0 mod 2))/2 &gt; ⌊(κ_0 + (1+(−1)^(κ_0 mod 2))/2)/2⌋+γ
µ+1 ≥ η ≥ max{2,µ+1}
µ ≥ γ
and
c := (a + b/2 + √(b(b+4a))/2)^(1/min{e_1,e_2}), where
c_0 := 4/(1−1/2^(η−1)−1/2^η)^2,
a := 2^(η+1)(1+c_0)/(2^(η−1)−1) &gt; 0,
b := 2^(µ+2) &gt; 0,
e_1 := log((κ_0+(3+(−1)^(κ_0 mod 2))/2)/(⌊(κ_0+(3+(−1)^(κ_0 mod 2))/2)/2⌋−γ+µ+1)),
e_2 := log((κ_0+(1+(−1)^(κ_0 mod 2))/2)/(⌈(κ_0+(1+(−1)^(κ_0 mod 2))/2)/2⌉+γ)).
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.Equation6 -->
[Statement.lean, lines 643–657](../Statement.lean#L643-L657)

<pre title="Statement.lean, lines 643–657">
/-- Theorem 11.1 (= Eq. (6) of Theorem 11.3), p.51: "(η, κ0, γ, μ) are any integers satisfying
min{⌊(κ0+1)/2⌋ − γ, ⌈(κ0+1)/2⌉ + γ} ≥ 1,
max{⌊(κ0+1)/2⌋ − γ + μ + 1, ⌈(κ0+1)/2⌉ + γ} ≤ κ0,
min{⌊(κ0+1)/2⌋ − γ + μ + 1, ⌈(κ0+1)/2⌉ + γ} ≥ η + 1,
κ0 + (3+(−1)^{κ0 mod 2})/2 &gt; ⌊(κ0 + (3+(−1)^{κ0 mod 2})/2)/2⌋ − γ + μ + 1,
κ0 + (1+(−1)^{κ0 mod 2})/2 &gt; ⌊(κ0 + (1+(−1)^{κ0 mod 2})/2)/2⌋ + γ,
μ + 1 ≥ η ≥ max{2, μ + 1}, μ ≥ γ". -/
def Equation6 (η κ0 γ μ : ℤ) : Prop :=
  min (floorHalf (κ0 + 1) - γ) (ceilHalf (κ0 + 1) + γ) ≥ 1 ∧
  max (floorHalf (κ0 + 1) - γ + μ + 1) (ceilHalf (κ0 + 1) + γ) ≤ κ0 ∧
  min (floorHalf (κ0 + 1) - γ + μ + 1) (ceilHalf (κ0 + 1) + γ) ≥ η + 1 ∧
  κ0 + sThree κ0 &gt; floorHalf (κ0 + sThree κ0) - γ + μ + 1 ∧
  κ0 + sOne κ0 &gt; floorHalf (κ0 + sOne κ0) + γ ∧
  μ + 1 ≥ η ∧ η ≥ max 2 (μ + 1) ∧
  μ ≥ γ
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.floorHalf -->
[Statement.lean, lines 633–634](../Statement.lean#L633-L634)

<pre title="Statement.lean, lines 633–634">
/-- `⌊z/2⌋`. -/
def floorHalf (z : ℤ) : ℤ := Int.fdiv z 2
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.ceilHalf -->
[Statement.lean, lines 635–636](../Statement.lean#L635-L636)

<pre title="Statement.lean, lines 635–636">
/-- `⌈z/2⌉`. -/
def ceilHalf (z : ℤ) : ℤ := -Int.fdiv (-z) 2
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.sThree -->
[Statement.lean, lines 638–639](../Statement.lean#L638-L639)

<pre title="Statement.lean, lines 638–639">
/-- `(3 + (−1)^{κ0 mod 2})/2`. -/
def sThree (κ0 : ℤ) : ℤ := Int.fdiv (3 + (-1) ^ (κ0 % 2).toNat) 2
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.sOne -->
[Statement.lean, lines 640–641](../Statement.lean#L640-L641)

<pre title="Statement.lean, lines 640–641">
/-- `(1 + (−1)^{κ0 mod 2})/2`. -/
def sOne (κ0 : ℤ) : ℤ := Int.fdiv (1 + (-1) ^ (κ0 % 2).toNat) 2
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.constC -->
[Statement.lean, lines 662–672](../Statement.lean#L662-L672)

<pre title="Statement.lean, lines 662–672">
/-- Theorem 11.1, p.51: "c := (a + b/2 + √(b(b+4a))/2)^{1/min{e1,e2}}, where c0 := 4/(1 − 1/2^{η−1} −
1/2^η)², a := 2^{η+1}(1+c0)/(2^{η−1} − 1), b := 2^{μ+2}, e1 := log((κ0 + (3+(−1)^{κ0 mod 2})/2) /
(⌊(κ0 + (3+(−1)^{κ0 mod 2})/2)/2⌋ − γ + μ + 1)), e2 := log((κ0 + (1+(−1)^{κ0 mod 2})/2) /
(⌈(κ0 + (1+(−1)^{κ0 mod 2})/2)/2⌉ + γ))". -/
noncomputable def constC (η κ0 γ μ : ℤ) : ℝ :=
  let c0 : ℝ := 4 / (1 - 1 / (2 : ℝ) ^ (η - 1) - 1 / (2 : ℝ) ^ η) ^ 2
  let a : ℝ := (2 : ℝ) ^ (η + 1) * (1 + c0) / ((2 : ℝ) ^ (η - 1) - 1)
  let b : ℝ := (2 : ℝ) ^ (μ + 2)
  let e1 : ℝ := Real.logb 2 (((κ0 + sThree κ0 : ℤ) : ℝ) / ((floorHalf (κ0 + sThree κ0) - γ + μ + 1 : ℤ) : ℝ))
  let e2 : ℝ := Real.logb 2 (((κ0 + sOne κ0 : ℤ) : ℝ) / ((ceilHalf (κ0 + sOne κ0) + γ : ℤ) : ℝ))
  (a + b / 2 + Real.sqrt (b * (b + 4 * a)) / 2) ^ (1 / min e1 e2)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.soundTerm -->
[Statement.lean, lines 674–676](../Statement.lean#L674-L676)

<pre title="Statement.lean, lines 674–676">
/-- `(2^{η+1} + κ^{log c}) / (1 − 2^{−η})`, the common term of both soundness functions of Theorem 11.1. -/
noncomputable def soundTerm (η κ0 γ μ : ℤ) (κ : ℕ) : ℝ :=
  ((2 : ℝ) ^ (η + 1) + (κ : ℝ) ^ Real.logb 2 (constC η κ0 γ μ)) / (1 - (2 : ℝ) ^ (-η))
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.Tuple -->
[Statement.lean, lines 684–689](../Statement.lean#L684-L689)

<pre title="Statement.lean, lines 684–689">
/-- A parameter tuple `(η, κ0, γ, μ)` (natural numbers). -/
structure Tuple where
  η : ℕ
  κ0 : ℕ
  γ : ℕ
  μ : ℕ
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.Tuple.Valid -->
[Statement.lean, lines 691–692](../Statement.lean#L691-L692)

<pre title="Statement.lean, lines 691–692">
/-- Eq. (6) for a natural tuple. -/
def Tuple.Valid (T : Tuple) : Prop := Equation6 T.η T.κ0 T.γ T.μ
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.Tuple.PositiveExponents -->
[Statement.lean, lines 694–699](../Statement.lean#L694-L699)

<pre title="Statement.lean, lines 694–699">
/-- The positive-exponent domain of `1/min{e1,e2}` in Theorem 11.1, p.51. -/
def Tuple.PositiveExponents (T : Tuple) : Prop :=
  0 &lt; Real.logb 2 (((T.κ0 + sThree T.κ0 : ℤ) : ℝ) /
    ((floorHalf (T.κ0 + sThree T.κ0) - T.γ + T.μ + 1 : ℤ) : ℝ)) ∧
  0 &lt; Real.logb 2 (((T.κ0 + sOne T.κ0 : ℤ) : ℝ) /
    ((ceilHalf (T.κ0 + sOne T.κ0) + T.γ : ℤ) : ℝ))
</pre>
<!-- /lean -->
<p>The published parameters are integers; the retained release tuple is natural. The separate positive-exponent condition states the domain on which the displayed reciprocal exponent is defined. Base-two logarithms are the documented transcription convention.</p>
</td></tr>
<tr><td>
<p><b>Polynomial evaluation, degree bounds, RS and VRS</b></p>
<p>BCGT ECCC TR12-045 revision 3, December 28, 2012; Definition 4.1; printed p. 18; PDF p. 18. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Mathematical notation transcribed from the rendered page; superscripts/subscripts are written using ^ and _, fractions using parentheses, with typographic line wrapping normalized.</i></p>

<pre>
Definition 4.1. Let 𝔽 be a field and S a subset of 𝔽. The evaluation of a polynomial P(x) = ∑_(i=0)^d a_i x^i over S is the function p : S → 𝔽 defined by p(s) = P(s) for all s ∈ S. The formal sum P(x) is called the polynomial corresponding to (the function) p. Similar definitions hold for multivariate polynomials.
</pre>
<p>BCGT ECCC TR12-045 revision 3, December 28, 2012; Definitions 4.2–4.4; printed p. 18; PDF p. 18. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>The wording and line wrapping of the pinned layout-text extraction are retained; blackboard field symbols are transcribed from the rendered pinned page.</i></p>

<pre>
Definition 4.2. Let 𝔽 be a field and d ≥ 0. A polynomial P (x) over 𝔽 has degree d if the
degree of P in x is at most d.

Definition 4.3. Let 𝔽 be a field, S a subset of 𝔽, and d ≥ 0. The Reed–Solomon code of
degree d over 𝔽 evaluated at S is the set of functions

RS(𝔽, S, d) := {p : S → 𝔽 s.t. p is an evaluation of a polynomial of degree at most d over S} .

Definition 4.4. Let 𝔽 be a field, S and H subsets of 𝔽, and d ≥ 0. The H-vanishing Reed–
Solomon code of degree d over 𝔽 evaluated at S is the set of functions

VRS(𝔽, S, H, d) := {p ∈ RS(𝔽, S, d) s.t. the polynomial corresponding to p vanishes on H} .
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.RS -->
[Statement.lean, lines 737–739](../Statement.lean#L737-L739)

<pre title="Statement.lean, lines 737–739">
/-- Def 4.3, "RS(F, S, d) := {p : S → F s.t. p is an evaluation of a polynomial of degree at most d over S}". -/
def RS (S : Finset F) (d : ℕ) : Set (F → F) :=
  {p | ∃ P : F[X], P.natDegree ≤ d ∧ ∀ s ∈ S, p s = P.eval s}
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.VRS -->
[Statement.lean, lines 741–743](../Statement.lean#L741-L743)

<pre title="Statement.lean, lines 741–743">
/-- Def 4.4, "VRS(F, S, H, d) := {p ∈ RS(F, S, d) s.t. the polynomial corresponding to p vanishes on H}". -/
def VRS (S H : Finset F) (d : ℕ) : Set (F → F) :=
  {p | ∃ P : F[X], P.natDegree ≤ d ∧ (∀ s ∈ S, p s = P.eval s) ∧ ∀ h ∈ H, P.eval h = 0}
</pre>
<!-- /lean -->
<p>The source’s phrase “has degree d” means degree at most d (Definition 4.2). The formal functions extend from a finite evaluation set to the whole ambient field; equality is required only on the named set, as the source states.</p>
</td></tr>
<tr><td>
<p><b>Fractional distance and distance to the RS code</b></p>
<p>BCGT ECCC TR12-045 revision 3, December 28, 2012; Definition 4.7; printed p. 18; PDF p. 18. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Mathematical notation transcribed from the rendered page; superscripts/subscripts are written using ^ and _, fractions using parentheses, with typographic line wrapping normalized.</i></p>
<p><b>Marked omissions:</b> The subsequent sentence about viewing strings as functions is omitted.</p>

<pre>
Definition 4.7. Let Σ be a finite alphabet and N a positive integer. For any two Σ-strings a and b in Σ^N, the fractional (Hamming) distance over the alphabet Σ between a and b, denoted Δ_N(a,b), is equal to the number of positions where a and b differ divided by N,
Δ_N(a,b) := |{i∈N : a_i ≠ b_i}|/N.
</pre>
<p>BCGT ECCC TR12-045 revision 3, December 28, 2012; Definition 4.8; printed p. 19; PDF p. 19. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Mathematical notation transcribed from the rendered page; superscripts/subscripts are written using ^ and _, fractions using parentheses, with typographic line wrapping normalized.</i></p>

<pre>
Definition 4.8. Let 𝔽 be a field, V a subset of 𝔽, f : V → 𝔽 a univariate function, and d ≥ 0. We denote by δ_V^(d)(f) the fractional Hamming distance of f to RS(𝔽,V,d), i.e.,
δ_V^(d)(f) := inf_(P∈𝔽[x], deg_x(P)≤d) Δ_V(f,P).
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.fracDist -->
[Statement.lean, lines 733–735](../Statement.lean#L733-L735)

<pre title="Statement.lean, lines 733–735">
/-- Def 4.7, fractional Hamming distance of functions on the evaluation set `S`. -/
noncomputable def fracDist (S : Finset F) (p q : F → F) : ℝ :=
  ((S.filter fun s =&gt; p s ≠ q s).card : ℝ) / (S.card : ℝ)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.RS -->
[Statement.lean, lines 737–739](../Statement.lean#L737-L739)

<pre title="Statement.lean, lines 737–739">
/-- Def 4.3, "RS(F, S, d) := {p : S → F s.t. p is an evaluation of a polynomial of degree at most d over S}". -/
def RS (S : Finset F) (d : ℕ) : Set (F → F) :=
  {p | ∃ P : F[X], P.natDegree ≤ d ∧ ∀ s ∈ S, p s = P.eval s}
</pre>
<!-- /lean -->
<p>The retained soundness is quantified over every codeword; on the finite source evaluation set this expresses the corresponding distance lower bound without an extra approximate-minimum choice.</p>
</td></tr>
<tr><td>
<p><b>The source PCPP vocabulary and strong completeness/soundness</b></p>
<p>BCGT ECCC TR12-045 revision 3, December 28, 2012; Paragraph defining an (r,q)-PCPP verifier; printed p. 20; PDF p. 20. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Mathematical notation transcribed from the rendered page; superscripts/subscripts are written using ^ and _, fractions using parentheses, with typographic line wrapping normalized.</i></p>

<pre>
For functions r,q : ℕ → ℕ we say that a probabilistic oracle machine V is a (r,q)-PCPP verifier if, given an explicit input x = (x′,N′) with |x′| = n and oracle access to an N-bit implicit input y and proof π, V runs in time 2^(O(r(n))), tosses r(n) coins, makes q(n) queries to (y,π), and outputs either 1 (“accept”) or 0 (“reject”).
</pre>
<p>BCGT ECCC TR12-045 revision 3, December 28, 2012; Definition 4.15; printed p. 20; PDF p. 20. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Mathematical notation transcribed from the rendered page; superscripts/subscripts are written using ^ and _, fractions using parentheses, with typographic line wrapping normalized.</i></p>

<pre>
Definition 4.15. Let s ∈ (0,1] × ℕ → (0,1] and r,q : ℕ → ℕ. A pair language L belongs to the class Strong-PCP_(s(δ,n))[r(n),q(n)] if there exists a (r,q)-PCPP verifier V_L such that the following holds:
1. (Perfect) Completeness: If (x,y) ∈ L then there exists π such that Pr_R[V_L^(y,π)(x;R) = 1] = 1.
2. Soundness: For every π it holds that Pr_R[V_L^(y,π)(x;R) = 1] ≤ 1−s(Δ(y,L_x),n).
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.FlatVerifier -->
[Statement.lean, lines 885–893](../Statement.lean#L885-L893)

<pre title="Statement.lean, lines 885–893">
/-- A verifier as §12.3 decomposes it: `rand` coins, `query` queries, proof `length` (field elements); `Q r i`
is the 1-based index of the `i`-th query into the concatenation of the implicit input (`|S|` entries) and the
proof, or `none` (`⊥`); `D r ans` decides from the answers `ans 1, ans 2, …`. -/
structure FlatVerifier (F : Type) where
  rand : ℕ
  query : ℕ
  length : ℕ
  Q : List Bool → ℕ → Option ℕ
  D : List Bool → (ℕ → F) → Bool
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.FlatVerifier.answers -->
[Statement.lean, lines 1007–1017](../Statement.lean#L1007-L1017)

<pre title="Statement.lean, lines 1007–1017">
/-- The answers to the queries of `V` on coins `r`, implicit input `p` (on `S` with basis `B`, offset `O`) and proof
`π`: index `j ∈ {1, …, |S|}` reads `p(GetEltWithIndex(B, O, j))`, index `|S| + 1 + t` reads `π t`; `⊥` and
indices out of range read `0`. -/
def FlatVerifier.answers (V : FlatVerifier F) (B : List F) (O : F) (p : F → F) (π : Fin V.length → F)
    (r : List Bool) (i : ℕ) : F :=
  match V.Q r i with
  | none =&gt; 0
  | some j =&gt;
    if 1 ≤ j ∧ j ≤ 2 ^ B.length then p (eltWithIndex B O j)
    else if h : j - 2 ^ B.length - 1 &lt; V.length ∧ 2 ^ B.length &lt; j then π ⟨j - 2 ^ B.length - 1, h.1⟩
    else 0
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.FlatVerifier.accepts -->
[Statement.lean, lines 1019–1022](../Statement.lean#L1019-L1022)

<pre title="Statement.lean, lines 1019–1022">
/-- `V^{(p,π)}(x; r)`. -/
def FlatVerifier.accepts (V : FlatVerifier F) (B : List F) (O : F) (p : F → F) (π : Fin V.length → F)
    (r : Fin V.rand → Bool) : Bool :=
  V.D (List.ofFn r) (V.answers B O p π (List.ofFn r))
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.FlatVerifier.acceptProb -->
[Statement.lean, lines 1024–1027](../Statement.lean#L1024-L1027)

<pre title="Statement.lean, lines 1024–1027">
/-- `Pr_R[V^{(p,π)}(x; R) = 1]` for uniform `R ∈ {0,1}^rand`. -/
noncomputable def FlatVerifier.acceptProb (V : FlatVerifier F) (B : List F) (O : F) (p : F → F)
    (π : Fin V.length → F) : ℝ :=
  ((univ.filter fun r =&gt; V.accepts B O p π r = true).card : ℝ) / (2 : ℝ) ^ V.rand
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1_Fixed -->
[Statement.lean, lines 1065–1087](../Statement.lean#L1065-L1087)

<pre title="Statement.lean, lines 1065–1087">
/-- **BCGT13 Theorem 11.1 at `(η, κ0, γ, μ) = (2, 4, 0, 1)`, with a weaker proof bound:** using
`1−2^{1−η}` for the distance in Lemma 11.10 and the product obtained from Corollary 11.13's τ algebra
(rather than the printed sum) gives `K(κ) = 16·κ^{log₂ c}`, RS denominator `1+K` and VRS denominator
`2+K` (ECCC rev. 3, pp.67–69).
The verifiers, constant `c`, completeness, degree ranges and all other quantifiers are unchanged, and
`bcgt13Fixed_of_theorem11_1` proves that the recorded printed statement implies this fixed release input. -/
def BCGT13_Theorem11_1_Fixed : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (ℓ : ℕ), Fintype.card F = 2 ^ ℓ →
  ∀ (B : List F) (O : F), IsBasis B O →
    -- V_RS on explicit input (I_ℓ, B_S, O_S, d), "d, positive integer indicating what “low-degree” means"
    -- (Algorithm 13 inputs, p.119; §12.3.4, p.82: "… and d is a positive integer")
    (∀ d : ℕ, 1 ≤ d → d &lt; 2 ^ B.length →
      (∀ p ∈ RS (span B O) d, ∃ π, ∀ r, (vRS Tuple.fixed B O d).accepts B O p π r = true) ∧
      ∀ (p : F → F) (π : Fin (vRS Tuple.fixed B O d).length → F) (δ : ℝ),
        (∀ q ∈ RS (span B O) d, δ ≤ fracDist (span B O) p q) →
        (vRS Tuple.fixed B O d).acceptProb B O p π ≤ 1 - δ / (1 + repairedSoundTerm B.length)) ∧
    -- V_VRS on explicit input (I_ℓ, B_S, O_S, B_H, O_H, d)
    (∀ (BH : List F) (OH : F), IsBasis BH OH → span BH OH ⊆ span B O →
     ∀ d : ℕ, 2 ^ BH.length ≤ d → d &lt; 2 ^ B.length →
      (∀ p ∈ VRS (span B O) (span BH OH) d, ∃ π, ∀ r, (vVRS Tuple.fixed B O BH OH d).accepts B O p π r = true) ∧
      ∀ (p : F → F) (π : Fin (vVRS Tuple.fixed B O BH OH d).length → F) (δ : ℝ),
        (∀ q ∈ VRS (span B O) (span BH OH) d, δ ≤ fracDist (span B O) p q) →
        (vVRS Tuple.fixed B O BH OH d).acceptProb B O p π ≤ 1 - δ / (2 + repairedSoundTerm B.length))
</pre>
<!-- /lean -->
<p>The table prints the source’s generic verifier convention as well as Definition 4.15. The retained BCGT premise contains the semantic completeness and soundness clauses for the named verifiers, without a separate running-time field; the physical constructor and its costs are supplied by proved adapters, as explained above.</p>
</td></tr>
<tr><td>
<p><b>Definition 12.14: non-adaptive PCPP verifier</b></p>
<p>ECCC TR12-045 revision 3, December 28, 2012; Definition 12.14; printed p. 75; PDF p. 75. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Transcribed against the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. Printed formulas, indices and conditions are retained without repair.</i></p>

<pre>
A PCPP verifier \(V\) is non-adaptive if its queries are based only on the explicit input and its internal coin tosses, independently of the answers given to previous queries. That is, \(V\) can be decomposed into a pair of algorithms \(Q\) and \(D\) such that on explicit input \(x\) and a random tape \(r\), the verifier makes the query sequence \(Q(x,r,1),\ldots,Q(x,r,p(|x|))\), obtains the answers \(b_1,\ldots,b_{p(|x|)}\), and decides according to \(D(x,r,b_1\cdots b_{p(|x|)})\), where \(p\) is some fixed polynomial.
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.FlatVerifier -->
[Statement.lean, lines 885–893](../Statement.lean#L885-L893)

<pre title="Statement.lean, lines 885–893">
/-- A verifier as §12.3 decomposes it: `rand` coins, `query` queries, proof `length` (field elements); `Q r i`
is the 1-based index of the `i`-th query into the concatenation of the implicit input (`|S|` entries) and the
proof, or `none` (`⊥`); `D r ans` decides from the answers `ans 1, ans 2, …`. -/
structure FlatVerifier (F : Type) where
  rand : ℕ
  query : ℕ
  length : ℕ
  Q : List Bool → ℕ → Option ℕ
  D : List Bool → (ℕ → F) → Bool
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.FlatVerifier.answers -->
[Statement.lean, lines 1007–1017](../Statement.lean#L1007-L1017)

<pre title="Statement.lean, lines 1007–1017">
/-- The answers to the queries of `V` on coins `r`, implicit input `p` (on `S` with basis `B`, offset `O`) and proof
`π`: index `j ∈ {1, …, |S|}` reads `p(GetEltWithIndex(B, O, j))`, index `|S| + 1 + t` reads `π t`; `⊥` and
indices out of range read `0`. -/
def FlatVerifier.answers (V : FlatVerifier F) (B : List F) (O : F) (p : F → F) (π : Fin V.length → F)
    (r : List Bool) (i : ℕ) : F :=
  match V.Q r i with
  | none =&gt; 0
  | some j =&gt;
    if 1 ≤ j ∧ j ≤ 2 ^ B.length then p (eltWithIndex B O j)
    else if h : j - 2 ^ B.length - 1 &lt; V.length ∧ 2 ^ B.length &lt; j then π ⟨j - 2 ^ B.length - 1, h.1⟩
    else 0
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.FlatVerifier.accepts -->
[Statement.lean, lines 1019–1022](../Statement.lean#L1019-L1022)

<pre title="Statement.lean, lines 1019–1022">
/-- `V^{(p,π)}(x; r)`. -/
def FlatVerifier.accepts (V : FlatVerifier F) (B : List F) (O : F) (p : F → F) (π : Fin V.length → F)
    (r : Fin V.rand → Bool) : Bool :=
  V.D (List.ofFn r) (V.answers B O p π (List.ofFn r))
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.FlatVerifier.acceptProb -->
[Statement.lean, lines 1024–1027](../Statement.lean#L1024-L1027)

<pre title="Statement.lean, lines 1024–1027">
/-- `Pr_R[V^{(p,π)}(x; R) = 1]` for uniform `R ∈ {0,1}^rand`. -/
noncomputable def FlatVerifier.acceptProb (V : FlatVerifier F) (B : List F) (O : F) (p : F → F)
    (π : Fin V.length → F) : ℝ :=
  ((univ.filter fun r =&gt; V.accepts B O p π r = true).card : ℝ) / (2 : ℝ) ^ V.rand
</pre>
<!-- /lean -->
<p>FlatVerifier records the separate query and decision functions, together with randomness, query count and proof length. The 1-based concatenated input/proof indexing, the optional query value, and zero answers outside the valid domain are explicit transcription conventions; they are not extra source quotations or efficiency claims.</p>
</td></tr>
<tr><td>
<p><b>Remark 12.15: field-element oracles</b></p>
<p>ECCC TR12-045 revision 3, December 28, 2012; Remark 12.15; printed p. 75; PDF p. 75. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Transcribed against the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. Printed formulas, indices and conditions are retained without repair.</i></p>

<pre>
Note that the alphabet of proof oracles (as well as implicit inputs) are elements of a finite field \(\mathbb{F}_{2^\ell}\), and not bits. Thus, our descriptions of \(Q\) and \(D\) will reason about indexing into strings of such field elements. The departure from binary oracles is mostly inconsequential, with the exception of a minor note that will come up later in the proof of almost universal arguments. (See Remark 12.41.)
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.FlatVerifier -->
[Statement.lean, lines 885–893](../Statement.lean#L885-L893)

<pre title="Statement.lean, lines 885–893">
/-- A verifier as §12.3 decomposes it: `rand` coins, `query` queries, proof `length` (field elements); `Q r i`
is the 1-based index of the `i`-th query into the concatenation of the implicit input (`|S|` entries) and the
proof, or `none` (`⊥`); `D r ans` decides from the answers `ans 1, ans 2, …`. -/
structure FlatVerifier (F : Type) where
  rand : ℕ
  query : ℕ
  length : ℕ
  Q : List Bool → ℕ → Option ℕ
  D : List Bool → (ℕ → F) → Bool
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.FlatVerifier.answers -->
[Statement.lean, lines 1007–1017](../Statement.lean#L1007-L1017)

<pre title="Statement.lean, lines 1007–1017">
/-- The answers to the queries of `V` on coins `r`, implicit input `p` (on `S` with basis `B`, offset `O`) and proof
`π`: index `j ∈ {1, …, |S|}` reads `p(GetEltWithIndex(B, O, j))`, index `|S| + 1 + t` reads `π t`; `⊥` and
indices out of range read `0`. -/
def FlatVerifier.answers (V : FlatVerifier F) (B : List F) (O : F) (p : F → F) (π : Fin V.length → F)
    (r : List Bool) (i : ℕ) : F :=
  match V.Q r i with
  | none =&gt; 0
  | some j =&gt;
    if 1 ≤ j ∧ j ≤ 2 ^ B.length then p (eltWithIndex B O j)
    else if h : j - 2 ^ B.length - 1 &lt; V.length ∧ 2 ^ B.length &lt; j then π ⟨j - 2 ^ B.length - 1, h.1⟩
    else 0
</pre>
<!-- /lean -->
<p>The flat oracle answers are field elements. Binary serialization and any conversion to ordinary machines are separate proved adapters; they are not attributed to this remark.</p>
</td></tr>
<tr><td>
<p><b>Algorithm 19: GetRandElt</b></p>
<p>ECCC TR12-045 revision 3, December 28, 2012; Algorithm 19, complete listing; printed p. 125; PDF p. 125. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Transcribed against the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. Printed formulas, indices and conditions are retained without repair.</i></p>

<pre>
inputs:
• \(I_\ell\), irreducible polynomial of degree \(\ell\) over \(\mathbb{F}_2\) with root \(\mathsf{x}\), inducing the field extension \(\mathbb{F}_{2^\ell}:=\mathbb{F}_2(\mathsf{x})\)
• \(\mathcal{B}_S=(a_1,\ldots,a_\kappa)\) and \(\mathcal{O}_S\), basis and offset for the \(\kappa\)-dimensional affine subspace \(S\subseteq\mathbb{F}_{2^\ell}\)
• \((r_1,\ldots,r_\kappa)\), random binary string used to select the element of \(S\)
output:
• \(\alpha\), selected element of \(S\)

1. \(\alpha:=(\sum_{j=1}^{\kappa}r_j a_j)+\mathcal{O}_S\)
2. output \(\alpha\)

notes:
• the random bits are simply the coefficients of the linear combination
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.getRandElt -->
[Statement.lean, lines 710–712](../Statement.lean#L710-L712)

<pre title="Statement.lean, lines 710–712">
/-- Algorithm 19 (GetRandElt): "α := Σ_{j=1}^κ r_j a_j + O_S" (missing bits read as 0, extra bits ignored). -/
def getRandElt (B : List F) (O : F) (r : List Bool) : F :=
  (List.zipWith (fun a b =&gt; if b then a else 0) B r).sum + O
</pre>
<!-- /lean -->
<p>The displayed field-linear combination is transcribed directly. Reading absent bits as zero and ignoring extra bits merely totalizes the Lean function outside the stated random-string length.</p>
</td></tr>
<tr><td>
<p><b>Algorithm 20: GetEltWithIndex</b></p>
<p>ECCC TR12-045 revision 3, December 28, 2012; Algorithm 20, complete listing; printed p. 125; PDF p. 125. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Transcribed against the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. Printed formulas, indices and conditions are retained without repair.</i></p>

<pre>
inputs:
• \(I_\ell\), irreducible polynomial of degree \(\ell\) over \(\mathbb{F}_2\) with root \(\mathsf{x}\), inducing the field extension \(\mathbb{F}_{2^\ell}:=\mathbb{F}_2(\mathsf{x})\)
• \(\mathcal{B}_S=(a_1,\ldots,a_\kappa)\) and \(\mathcal{O}_S\), basis and offset for the \(\kappa\)-dimensional affine subspace \(S\subseteq\mathbb{F}_{2^\ell}\)
• \(i\), index in \(\{1,\ldots,2^\kappa\}\) of the desired element of \(S\)
output:
• \(\alpha\), selected element of \(S\)

1. \(\alpha:=(\sum_{j=1}^{\kappa}i_j a_j)+\mathcal{O}_S\)
2. output \(\alpha\)

notes:
• \(i_1\cdots i_\kappa\) is \((i-1)\) in binary
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.eltWithIndex -->
[Statement.lean, lines 714–717](../Statement.lean#L714-L717)

<pre title="Statement.lean, lines 714–717">
/-- Algorithm 20 (GetEltWithIndex): "α := (Σ_{j=1}^κ i_j a_j) + O_S, … i_1 ⋯ i_κ is (i − 1) in binary"
(least significant bit first, see the header). -/
def eltWithIndex (B : List F) (O : F) (i : ℕ) : F :=
  getRandElt B O ((List.range B.length).map fun j =&gt; (i - 1).testBit j)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.indexOfElt -->
[Statement.lean, lines 719–721](../Statement.lean#L719-L721)

<pre title="Statement.lean, lines 719–721">
/-- GetIndexOfElt: the least `i ∈ {1, …, 2^κ}` with `GetEltWithIndex(B, O, i) = α`, and `0` if there is none. -/
def indexOfElt (B : List F) (O : F) (α : F) : ℕ :=
  (((List.range (2 ^ B.length)).find? fun i =&gt; eltWithIndex B O (i + 1) = α).map (· + 1)).getD 0
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.span -->
[Statement.lean, lines 723–725](../Statement.lean#L723-L725)

<pre title="Statement.lean, lines 723–725">
/-- The affine subspace with basis `B` and offset `O`: its `2^κ` points in GetEltWithIndex order. -/
def span (B : List F) (O : F) : Finset F :=
  ((List.range (2 ^ B.length)).map fun i =&gt; eltWithIndex B O (i + 1)).toFinset
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.IsBasis -->
[Statement.lean, lines 727–728](../Statement.lean#L727-L728)

<pre title="Statement.lean, lines 727–728">
/-- "`B_S` and `O_S`, basis and offset for the `κ`-dimensional affine subspace `S`": the points are distinct. -/
def IsBasis (B : List F) (O : F) : Prop := (span B O).card = 2 ^ B.length
</pre>
<!-- /lean -->
<p>Lean fixes the bit order to least significant first and defines the inverse index by the same finite enumeration, returning zero if no index exists. These ordering and off-domain choices are recorded conventions. IsBasis states that the enumeration contains exactly 2^κ distinct points.</p>
</td></tr>
<tr><td>
<p><b>Algorithm 21: FindSubspPoly output</b></p>
<p>ECCC TR12-045 revision 3, December 28, 2012; Algorithm 21, inputs and output specification; printed p. 126; PDF p. 126. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Transcribed against the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. Printed formulas, indices and conditions are retained without repair.</i></p>
<p><b>Marked omissions:</b> Algorithm 21 steps 1–3 and its subsequent recursion notes are omitted after this complete input/output specification. No edited version of those steps is quoted.</p>

<pre>
inputs:
• \(I_\ell\), irreducible polynomial of degree \(\ell\) over \(\mathbb{F}_2\) with root \(\mathsf{x}\), inducing the field extension \(\mathbb{F}_{2^\ell}:=\mathbb{F}_2(\mathsf{x})\)
• \(\mathcal{B}_S=(a_1,\ldots,a_\kappa)\) and \(\mathcal{O}_S\), basis and offset for the \(\kappa\)-dimensional affine subspace \(S\subseteq\mathbb{F}_{2^\ell}\)
output:
• \([Z_S]^{\mathsf A}\), an \(O(\kappa)\) arithmetic circuit for computing \(Z_S(x)=\sum_{i=0}^{\kappa}\beta_i x^{2^i}+\gamma\), the vanishing polynomial for the affine subspace \(S\)
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.zEval -->
[Statement.lean, lines 730–731](../Statement.lean#L730-L731)

<pre title="Statement.lean, lines 730–731">
/-- Algorithm 21 (FindSubspPoly): the value of "the vanishing polynomial for the affine subspace S". -/
def zEval (B : List F) (O : F) (x : F) : F := ∏ s ∈ span B O, (x - s)
</pre>
<!-- /lean -->
<p>zEval denotes the value of the vanishing polynomial. This row does not assume the printed circuit construction or its complexity bound; it records the named output used by the mathematical verifier.</p>
</td></tr>
<tr><td>
<p><b>Algorithm 23: SubspaceInterp output</b></p>
<p>ECCC TR12-045 revision 3, December 28, 2012; Algorithm 23, inputs and output specification; printed p. 128; PDF p. 128. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Transcribed against the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. Printed formulas, indices and conditions are retained without repair.</i></p>
<p><b>Marked omissions:</b> Algorithm 23 step 1, the recursive definition of A, and its final note are omitted after this complete printed input/output specification. No repaired recursive listing is substituted.</p>

<pre>
inputs:
• \(I_\ell\), irreducible polynomial of degree \(\ell\) over \(\mathbb{F}_2\) with root \(\mathsf{x}\), inducing the field extension \(\mathbb{F}_{2^\ell}:=\mathbb{F}_2(\mathsf{x})\)
• \(\mathcal{B}_S=(a_1,\ldots,a_\kappa)\) and \(\mathcal{O}_S\), basis and offset for the \(\kappa\)-dimensional affine subspace \(S\subseteq\mathbb{F}_{2^\ell}\)
• \((\alpha_0,\ldots,\alpha_{2^\kappa-1})\), elements in \(\mathbb{F}_{2^\ell}\)
output:
• \(P(x)=\sum_{i=0}^{d}\beta_i x^i\), with \(d&lt;2^\kappa\), such that \(P(\sum_{i=1}^{\kappa}b_i a_i)=\alpha_{\sum_{i=i}^{\kappa}b_i2^{i-1}}\) for \(b_1\cdots b_\kappa\in\{0,1\}^{\kappa}\)
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.degreeTest -->
[Statement.lean, lines 745–749](../Statement.lean#L745-L749)

<pre title="Statement.lean, lines 745–749">
/-- The base-case test: the answers `α_1, …, α_{2^κ}` are, in GetEltWithIndex order, the values on the subspace
of a polynomial of degree at most `deg` (SubspaceInterp, then "if d̃ ≤ d, output 1, else output 0"). -/
noncomputable def degreeTest (B : List F) (O : F) (deg : ℕ) (ans : ℕ → F) : Bool :=
  @decide (∃ P : F[X], P.natDegree ≤ deg ∧ ∀ i &lt; 2 ^ B.length, P.eval (eltWithIndex B O (i + 1)) = ans (i + 1))
    (Classical.propDecidable _)
</pre>
<!-- /lean -->
<p>The source output line is reproduced as printed, including its sum subscript i=i and absence of an offset in that displayed interpolation argument. The Lean degreeTest uses the mathematical interpolation condition on the actual affine points from eltWithIndex; the existing convention/deviation discussion is retained outside the quotation. No printed recursive implementation is imported here.</p>
</td></tr>
<tr><td>
<p><b>Algorithm 12: V_VRS</b></p>
<p>ECCC TR12-045 revision 3, December 28, 2012; Algorithm 12, complete listing; printed p. 118; PDF p. 118. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Transcribed against the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. Printed formulas, indices and conditions are retained without repair.</i></p>

<pre>
inputs:
• \(I_\ell\), irreducible polynomial of degree \(\ell\) over \(\mathbb{F}_2\) with root \(\mathsf{x}\), inducing the field extension \(\mathbb{F}_{2^\ell}:=\mathbb{F}_2(\mathsf{x})\)
• \(\mathcal{B}_S\) and \(\mathcal{O}_S\), basis and offset for the \(\kappa\)-dimensional affine subspace \(S\subseteq\mathbb{F}_{2^\ell}\)
• \(\mathcal{B}_H\) and \(\mathcal{O}_H\), basis and offset for the \(\lambda\)-dimensional affine subspace \(H\subseteq\mathbb{F}_{2^\ell}\)
• \(d\), positive integer indicating what “low-degree” means
randomness:
• \(r_1\cdots r_{\operatorname{rand}_{\mathrm{VRS}}(\ell,\kappa,\lambda,d)}\)
oracles:
• \(p\), function from \(S\) to \(\mathbb{F}_{2^\ell}\)
• \(\pi=(\widetilde p,\widetilde\pi)\), proof of proximity to \(\mathrm{VRS}(\mathbb{F}_{2^\ell},S,H,d)\) for the function \(p\)

1. Proximity test of \(\widetilde p\) to \(\mathrm{RS}(\mathbb{F}_{2^\ell},S,d-|H|)\):
   (a) \(r'_1\cdots r'_{\operatorname{rand}_{\mathrm{RS}}(\ell,\kappa,d-|H|)}:=r_1\cdots r_{\operatorname{rand}_{\mathrm{RS}}(\ell,\kappa,d-|H|)}\)
   (b) \(b_{\mathrm{RS}}:=V_{\mathrm{RS}}^{(\widetilde p,\widetilde\pi)}(I_\ell,\mathcal B_S,\mathcal O_S,d-|H|;r'_1\cdots r'_{\operatorname{rand}_{\mathrm{RS}}(\ell,\kappa,d-|H|)})\)
2. Consistency check between \(p\) and \(\widetilde p\):
   (a) \(r_1^{(\alpha)}\cdots r_\kappa^{(\alpha)}:=r_1\cdots r_\kappa\)
   (b) \(\alpha:=\operatorname{GetRandElt}(I_\ell,\mathcal B_S,\mathcal O_S,(r_1^{(\alpha)},\ldots,r_\kappa^{(\alpha)}))\)
   (c) query \(\alpha\) to \(p\)
   (d) query \(\alpha\) to \(\widetilde p\)
   (e) \([Z_H]^{\mathsf A}:=\operatorname{FindSubspPoly}(I_\ell,\mathcal B_H,\mathcal O_H)\)
   (f) \(\omega:=[Z_H]^{\mathsf A}(\alpha)\)
   (g) if \((p(\alpha)=\omega\cdot\widetilde p(\alpha))\), then \(b_{\mathrm{consist}}:=1\), else \(b_{\mathrm{consist}}:=0\)
3. \(b:=b_{\mathrm{RS}}\wedge b_{\mathrm{consist}}\)
4. output \(b\)

notes:
• see Lemma C.5 for complexity bounds on queries and randomness
• see Lemma 12.20 for the “non-adaptive decomposition” of \(V_{\mathrm{VRS}}\) into \(Q_{\mathrm{VRS}}\) and \(D_{\mathrm{VRS}}\)
• see Algorithm 3 for \(P_{\mathrm{VRS}}\), the corresponding prover
• it must be that \(d\ge|H|\), otherwise \(p\) is certainly not in \(\mathrm{VRS}(\mathbb{F}_{2^\ell},S,H,d)\)
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.vVRS -->
[Statement.lean, lines 984–1005](../Statement.lean#L984-L1005)

<pre title="Statement.lean, lines 984–1005">
/-- `V_VRS` on `(I_ℓ, B_S, O_S, B_H, O_H, d)`, §12.3.5 (`Q_VRS`) with the decision of Algorithm 12 (see the
header): the proof is `(p̃, π̃)`; `V_RS` tests `p̃` against degree `d − |H|`; then `p(α) = Z_H(α)·p̃(α)`. -/
noncomputable def vVRS (T : Tuple) (B : List F) (O : F) (BH : List F) (OH : F) (d : ℕ) : FlatVerifier F :=
  let κ := B.length
  let nS := 2 ^ κ
  let V := vRS T B O (d - 2 ^ BH.length)
  { rand := max V.rand κ
    query := V.query + 2
    length := nS + V.length
    Q := fun r i =&gt;
      if 1 ≤ i ∧ i ≤ V.query then (V.Q r i).map fun j =&gt; nS + j      -- 1. j := |S| + j_old
      else
        let α := getRandElt B O (r.take κ)
        if i = V.query + 1 then some (indexOfElt B O α)               -- 2. query α to p
        else if i = V.query + 2 then some (nS + indexOfElt B O α)      -- 3. query α to p̃
        else none
    D := fun r ans =&gt;
      let bRS := V.D r ans                                            -- 3. b_RS
      let α := getRandElt B O (r.take κ)                              -- 4.–5.
      let τ := zEval BH OH α                                          -- 6.–7.
      -- Algorithm 12 step 2(g): "if p(α) = ω · p̃(α), then b_consist := 1"
      bRS &amp;&amp; decide (ans (V.query + 1) = τ * ans (V.query + 2)) }
</pre>
<!-- /lean -->
<p>This is the printed Algorithm 12 listing, including its consistency test p(α)=ω·p̃(α). The recorded transcription follows that decision rule; the existing comparison with the non-adaptive decomposition stays outside the quotation.</p>
</td></tr>
<tr><td>
<p><b>Algorithm 13: V_RS</b></p>
<p>ECCC TR12-045 revision 3, December 28, 2012; Algorithm 13, complete listing; printed p. 119; PDF p. 119. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Transcribed against the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. Printed formulas, indices and conditions are retained without repair.</i></p>

<pre>
inputs:
• \(I_\ell\), irreducible polynomial of degree \(\ell\) over \(\mathbb{F}_2\) with root \(\mathsf{x}\), inducing the field extension \(\mathbb{F}_{2^\ell}:=\mathbb{F}_2(\mathsf{x})\)
• \(\mathcal{B}_S\) and \(\mathcal{O}_S\), basis and offset for the \(\kappa\)-dimensional affine subspace \(S\subseteq\mathbb{F}_{2^\ell}\)
• \(d\), positive integer indicating what “low-degree” means
randomness:
• \(r_1\cdots r_{\operatorname{rand}_{\mathrm{RS}}(\ell,\kappa,d)}\)
oracles:
• \(p\), function from \(S\) to \(\mathbb{F}_{2^\ell}\)
• \(\pi\), proof of proximity to \(\mathrm{RS}(\mathbb{F}_{2^\ell},S,d)\) for the function \(p\)

1. if \(\kappa\le\eta\), then:
   (a) for \(i=1,\ldots,2^\kappa\):
       i. \(\alpha_i:=\operatorname{GetEltWithIndex}(I_\ell,\mathcal B_S,\mathcal O_S,i)\)
       ii. query \(\alpha_i\) to \(p\)
   (b) \(P:=\operatorname{SubspaceInterp}(I_\ell,\mathcal B_S,\mathcal O_S,(p(\alpha_1),\ldots,p(\alpha_{2^\kappa})))\)
   (c) \(\widetilde d:=\deg(P)\)
   (d) if \(\widetilde d\le d\), output \(1\), else output \(0\)
2. if \(\kappa&gt;\eta\), then:
   (a) \(d_{\kappa,\eta}:=|S|/2^\eta-1=2^\kappa/2^\eta-1\)
   (b) if \(d&lt;d_{\kappa,\eta}\), then output \(b:=V_{\mathrm{RS},&lt;}^{(p,\pi)}(I_\ell,\mathcal B_S,\mathcal O_S,d;r_1\cdots r_{\operatorname{rand}_{\mathrm{RS},&lt;}(\ell,\kappa,d)})\)
   (c) if \(d=d_{\kappa,\eta}\), then output \(b:=V_{\mathrm{RS},=}^{(p,\pi)}(I_\ell,\mathcal B_S,\mathcal O_S;r_1\cdots r_{\operatorname{rand}_{\mathrm{RS},=}(\ell,\kappa)})\)
   (d) if \(d&gt;d_{\kappa,\eta}\), then output \(b:=V_{\mathrm{RS},&gt;}^{(p,\pi)}(I_\ell,\mathcal B_S,\mathcal O_S,d;r_1\cdots r_{\operatorname{rand}_{\mathrm{RS},&gt;}(\ell,\kappa,d)})\)

notes:
• see Lemma C.4 for complexity bounds on queries and randomness
• see Lemma 12.19 for the “non-adaptive decomposition” of \(V_{\mathrm{RS}}\) into \(Q_{\mathrm{RS}}\) and \(D_{\mathrm{RS}}\)
• see Algorithm 4 for \(P_{\mathrm{RS}}\), the corresponding prover
• if \(\kappa\le\eta\), then \(V_{\mathrm{RS}}\) can just check directly whether \(p\) is in \(\mathrm{RS}(\mathbb{F}_{2^\ell},S,d)\) or not
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.vRS -->
[Statement.lean, lines 974–982](../Statement.lean#L974-L982)

<pre title="Statement.lean, lines 974–982">
/-- `V_RS` on `(I_ℓ, B_S, O_S, d)`, §12.3.4 (`Q_RS`, `D_RS`; Algorithm 13): for `κ ≤ η` the direct degree test
(`Q`: "output j := i"; `D`: SubspaceInterp and "if d̃ ≤ d output 1"), otherwise `V_{RS,&lt;}`, `V_{RS,=}`, `V_{RS,&gt;}`
as `d &lt;`, `=`, `&gt; d_{κ,η}`. -/
noncomputable def vRS (T : Tuple) (B : List F) (O : F) (d : ℕ) : FlatVerifier F :=
  if B.length ≤ T.η then
    { rand := 0, query := 2 ^ B.length, length := 0, Q := fun _ i =&gt; some i, D := fun _ ans =&gt; degreeTest B O d ans }
  else if d &lt; dKE B.length T.η then vLt T B O d
  else if d = dKE B.length T.η then vEq T B O
  else vGt T B O d
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.dKE -->
[Statement.lean, lines 755–756](../Statement.lean#L755-L756)

<pre title="Statement.lean, lines 755–756">
/-- `d_{κ,η} := |S|/2^η − 1 = 2^κ/2^η − 1`. -/
def dKE (κ η : ℕ) : ℕ := 2 ^ κ / 2 ^ η - 1
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.degreeTest -->
[Statement.lean, lines 745–749](../Statement.lean#L745-L749)

<pre title="Statement.lean, lines 745–749">
/-- The base-case test: the answers `α_1, …, α_{2^κ}` are, in GetEltWithIndex order, the values on the subspace
of a polynomial of degree at most `deg` (SubspaceInterp, then "if d̃ ≤ d, output 1, else output 0"). -/
noncomputable def degreeTest (B : List F) (O : F) (deg : ℕ) (ans : ℕ → F) : Bool :=
  @decide (∃ P : F[X], P.natDegree ≤ deg ∧ ∀ i &lt; 2 ^ B.length, P.eval (eltWithIndex B O (i + 1)) = ans (i + 1))
    (Classical.propDecidable _)
</pre>
<!-- /lean -->
<p>The printed positive-degree input condition and its three degree branches are preserved. The typed Lean function is totalized, while the retained theorem states its source degree range explicitly.</p>
</td></tr>
<tr><td>
<p><b>Algorithm 14: V_RS,&gt;</b></p>
<p>ECCC TR12-045 revision 3, December 28, 2012; Algorithm 14, complete listing; printed p. 120; PDF p. 120. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Transcribed against the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. Printed formulas, indices and conditions are retained without repair.</i></p>

<pre>
inputs:
• \(I_\ell\), irreducible polynomial of degree \(\ell\) over \(\mathbb{F}_2\) with root \(\mathsf{x}\), inducing the field extension \(\mathbb{F}_{2^\ell}:=\mathbb{F}_2(\mathsf{x})\)
• \(\mathcal{B}_S\) and \(\mathcal{O}_S\), basis and offset for the \(\kappa\)-dimensional affine subset \(S\subseteq\mathbb{F}_{2^\ell}\)
• \(d\), positive integer, greater than \(|S|/2^\eta-1\), indicating what “low-degree” means
randomness:
• \(r_1\cdots r_{\operatorname{rand}_{\mathrm{RS},&gt;}(\ell,\kappa,d)}\)
oracles:
• \(p\), function from \(S\) to \(\mathbb{F}_{2^\ell}\)
• \(\pi=((p_0,\pi_0),\ldots,(p_{2^\eta-1},\pi_{2^\eta-1}))\), proof of proximity to \(\mathrm{RS}(\mathbb{F}_{2^\ell},S,d)\) for the function \(p\)

1. if \(d\ge|S|\), then output \(b:=1\)
2. if \(d&lt;|S|\), then:
   (a) \(d_{\kappa,\eta}:=|S|/2^\eta-1=2^\kappa/2^\eta-1\)
   (b) \(m_{\kappa,\eta,d}:=\lfloor(d+1)/(d_{\kappa,\eta}+1)\rfloor\)
   (c) \(r_1^{(\tau)}\cdots r_\kappa^{(\tau)}:=r_1\cdots r_\kappa\)
   (d) \(\tau:=\operatorname{GetRandElt}(I_\ell,\mathcal B_S,\mathcal O_S,(r_1^{(\tau)},\ldots,r_\kappa^{(\tau)}))\)
   (e) query \(\tau\) to \(p\)
   (f) for \(i=0,\ldots,m_{\kappa,\eta,d}-1\):
       i. \(r_1^{(i)}\cdots r_{\operatorname{rand}_{\mathrm{RS},=}(\ell,\kappa)}^{(i)}:=r_1\cdots r_{\operatorname{rand}_{\mathrm{RS},=}(\ell,\kappa)}\)
       ii. query \(\tau\) to \(p_i\)
       iii. \(b_i:=V_{\mathrm{RS},=}^{(p_i,\pi_i)}(I_\ell,\mathcal B_S,\mathcal O_S,d_{\kappa,\eta};r_1^{(i)}\cdots r_{\operatorname{rand}_{\mathrm{RS},=}(\ell,\kappa)}^{(i)})\)
   (g) if \(m_{\kappa,\eta,d}\cdot(d_{\kappa,\eta}+1)=d+1\), then:
       i. \(\omega_\tau:=\sum_{i=0}^{m-1}\tau^{i(d_{\kappa,\eta}+1)}\cdot p_i(\tau)\)
       ii. if \(p(\tau)=\omega_\tau\), then \(b_{\mathrm{consist}}:=1\), else \(b_{\mathrm{consist}}:=0\)
       iii. \(b:=b_0\wedge\cdots\wedge b_{m_{\kappa,\eta,d}-1}\wedge b_{\mathrm{consist}}\)
       iv. output \(b\)
   (h) if \(m_{\kappa,\eta,d}\cdot(d_{\kappa,\eta}+1)&lt;d+1\), then:
       i. \(d_{\kappa,\eta,d}:=d-m_{\kappa,\eta,d}\cdot(d_{\kappa,\eta}+1)\)
       ii. \(r_1^{(m_{\kappa,\eta,d})}\cdots r_{\operatorname{rand}_{\mathrm{RS},&lt;}(\ell,\kappa,d_{\kappa,\eta,d})}^{(m_{\kappa,\eta,d})}:=r_1\cdots r_{\operatorname{rand}_{\mathrm{RS},&lt;}(\ell,\kappa,d_{\kappa,\eta,d})}\)
       iii. \(b_{m_{\kappa,\eta,d}}:=V_{\mathrm{RS},&lt;}^{(p_{m_{\kappa,\eta,d}},\pi_{m_{\kappa,\eta,d}})}(I_\ell,\mathcal B_S,\mathcal O_S,d_{\kappa,\eta,d};r_1^{(m_{\kappa,\eta,d})}\cdots r_{\operatorname{rand}_{\mathrm{RS},&lt;}(\ell,\kappa,d_{\kappa,\eta,d})}^{(m_{\kappa,\eta,d})})\)
       iv. query \(\tau\) to \(p_{m_{\kappa,\eta,d}}\)
       v. \(\omega_\tau:=\sum_{i=0}^{m_{\kappa,\eta,d}}\tau^{i(d_{\kappa,\eta}+1)}\cdot p_i(\tau)\)
       vi. if \(p(\tau)=\omega_\tau\), then \(b_{\mathrm{consist}}:=1\), else \(b_{\mathrm{consist}}:=0\)
       vii. \(b:=b_0\wedge\cdots\wedge b_{m_{\kappa,\eta,d}-1}\wedge b_{m_{\kappa,\eta,d}}\wedge b_{\mathrm{consist}}\)
       viii. output \(b\)

notes:
• see Lemma C.3 for complexity bounds on queries and randomness
• see Lemma 12.18 for the “non-adaptive decomposition” of \(V_{\mathrm{RS},&gt;}\) into \(Q_{\mathrm{RS},&gt;}\) and \(D_{\mathrm{RS},&gt;}\)
• see Algorithm 5 for \(P_{\mathrm{RS},&gt;}\), the corresponding prover
• if \(d\ge|S|\), every function \(p:S\to\mathbb{F}_{2^\ell}\) is in \(\mathrm{RS}(\mathbb{F}_{2^\ell},S,d)\) (cf. Step 1)
• if \(d&lt;|S|\), then \(\lfloor(d+1)/(d_{\kappa,\eta}+1)\rfloor\in\{0,\ldots,2^\eta\}\), because \(|S|=2^\eta\cdot(d_{\kappa,\eta}+1)\)
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.vGt -->
[Statement.lean, lines 931–972](../Statement.lean#L931-L972)

<pre title="Statement.lean, lines 931–972">
/-- `V_{RS,&gt;}` on `(I_ℓ, B_S, O_S, d)`, §12.3.3 (`Q_{RS,&gt;}`, `D_{RS,&gt;}`; Algorithm 14), for `d &lt; 2^κ`. -/
noncomputable def vGt (T : Tuple) (B : List F) (O : F) (d : ℕ) : FlatVerifier F :=
  let κ := B.length
  let nS := 2 ^ κ
  let D' := dKE κ T.η
  let m := mKED κ T.η d                              -- (b)
  let dd := d - m * (D' + 1)                         -- (c) d_{κ,η,d}
  let one : Bool := decide (m * (D' + 1) &lt; d + 1)
  let qE := queryEq T κ
  let lE := lengthEq T κ
  let vL := vLt T B O dd
  let qL := if one then vL.query else 0
  { rand := max (max (randEq T κ) (if one then randEq T κ else 0)) κ
    query := m * qE + qL + 1 + 2 ^ T.η
    length := m * (nS + lE) + (if one then nS + vL.length else 0)
    Q := fun r i =&gt;
      if d ≥ nS then none                            -- 1. output ⊥
      else if 1 ≤ i ∧ i ≤ m * qE then                -- (d)
        let zz := (i - 1) / qE
        (qEq T B O r (i - zz * qE)).map fun j' =&gt; nS + zz * (nS + lE) + j'
      else if one ∧ 1 ≤ i - m * qE ∧ i - m * qE ≤ qL then   -- (e)
        (vL.Q r (i - m * qE)).map fun j' =&gt; nS + m * (nS + lE) + j'
      else                                            -- (f), (g): the consistency queries
        let i0 := i - (m * qE + qL)
        let γ := getRandElt B O (r.take κ)
        let ιγ := indexOfElt B O γ
        if i0 = 1 then some ιγ
        else if 1 &lt; i0 ∧ i0 ≤ m + 1 then some (nS + (i0 - 2) * (nS + lE) + ιγ)
        else if one ∧ i0 = m + 2 then some (nS + m * (nS + lE) + ιγ)
        else none
    D := fun r ans =&gt;
      if d ≥ nS then true                            -- 1. output 1
      else
        let γ := getRandElt B O (r.take κ)           -- (a), (b)
        -- ii. b_i := D_{RS,=}(…, α^{(i)}) for i &lt; m; iv. b_m := D_{RS,&lt;}(…, α^{(m)}) when 𝟏 = 1
        let bs := (List.range m).all fun z =&gt; dEq T B O r fun i =&gt; ans (z * qE + i)
        let bm := if one then vL.D r (fun i =&gt; ans (m * qE + i)) else true
        -- v. b_consist := (v = Σ_{i=0}^{2^η−1} γ^{i(d_{κ,η}+1)} v_i), with ⊥-answers 0
        let base := m * qE + qL
        let v := ans (base + 1)
        let bc := decide (v = ∑ i ∈ Finset.range (2 ^ T.η), γ ^ (i * (D' + 1)) * ans (base + 2 + i))
        bc &amp;&amp; bs &amp;&amp; bm }
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.dKE -->
[Statement.lean, lines 755–756](../Statement.lean#L755-L756)

<pre title="Statement.lean, lines 755–756">
/-- `d_{κ,η} := |S|/2^η − 1 = 2^κ/2^η − 1`. -/
def dKE (κ η : ℕ) : ℕ := 2 ^ κ / 2 ^ η - 1
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.mKED -->
[Statement.lean, lines 758–759](../Statement.lean#L758-L759)

<pre title="Statement.lean, lines 758–759">
/-- `m_{κ,η,d} := ⌊(d+1)/(d_{κ,η}+1)⌋` (Algorithm 14 step 2(b); §12.3.3). -/
def mKED (κ η d : ℕ) : ℕ := (d + 1) / (dKE κ η + 1)
</pre>
<!-- /lean -->
<p>The floor defining m and both branches are reproduced from Algorithm 14. In particular, the printed extra d_{κ,η} argument in step 2(f)iii and the unsubscripted m in step 2(g)i are not silently normalized inside the source quotation. Existing transcription conventions remain outside it.</p>
</td></tr>
<tr><td>
<p><b>Algorithm 15: V_RS,&lt;</b></p>
<p>ECCC TR12-045 revision 3, December 28, 2012; Algorithm 15, complete listing; printed p. 121; PDF p. 121. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Transcribed against the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. Printed formulas, indices and conditions are retained without repair.</i></p>

<pre>
inputs:
• \(I_\ell\), irreducible polynomial of degree \(\ell\) over \(\mathbb{F}_2\) with root \(\mathsf{x}\), inducing the field extension \(\mathbb{F}_{2^\ell}:=\mathbb{F}_2(\mathsf{x})\)
• \(\mathcal{B}_S\) and \(\mathcal{O}_S\), basis for the \(\kappa\)-dimensional affine subset \(S\subseteq\mathbb{F}_{2^\ell}\)
• \(d\), positive integer, less than \(|S|/2^\eta-1\), indicating what “low-degree” means
randomness:
• \(r_1\cdots r_{\operatorname{rand}_{\mathrm{RS},&lt;}(\ell,\kappa,d)}\)
oracles:
• \(p\), function from \(S\) to \(\mathbb{F}_{2^\ell}\)
• \(\pi=(\pi_1,\pi_2)\), proof of proximity to \(\mathrm{RS}(\mathbb{F}_{2^\ell},S,d)\) for the function \(p\)

1. \(d_{\kappa,\eta}:=|S|/2^\eta-1=2^\kappa/2^\eta-1\)
2. \(r'_1\cdots r'_{\operatorname{rand}_{\mathrm{RS},=}(\ell,\kappa)}:=r_1\cdots r_{\operatorname{rand}_{\mathrm{RS},=}(\ell,\kappa)}\)
3. \(b_1:=V_{\mathrm{RS},=}^{(p,\pi_1)}(I_\ell,\mathcal B_S,\mathcal O_S;r'_1\cdots r'_{\operatorname{rand}_{\mathrm{RS},=}(\ell,\kappa)})\)
4. \(r''_1\cdots r''_{\operatorname{rand}_{\mathrm{RS},=}(\ell,\kappa)}:=r_1\cdots r_{\operatorname{rand}_{\mathrm{RS},=}(\ell,\kappa)}\)
5. compute the polynomial \(Q(x):=x^{d_{\kappa,\eta}-d}\in\mathbb{F}_{2^\ell}[x]\)
6. “\(p':=p\cdot Q\)” (see notes below)
7. \(b_2:=V_{\mathrm{RS},=}^{(p',\pi_2)}(I_\ell,\mathcal B_S,\mathcal O_S;r''_1\cdots r''_{\operatorname{rand}_{\mathrm{RS},=}(\ell,\kappa)})\)
8. \(b:=b_1\wedge b_2\)
9. output \(b\)

notes:
• see Lemma C.2 for complexity bounds on queries and randomness
• see Lemma 12.17 for the “non-adaptive decomposition” of \(V_{\mathrm{RS},&lt;}\) into \(Q_{\mathrm{RS},&lt;}\) and \(D_{\mathrm{RS},&lt;}\)
• see Algorithm 6 for \(P_{\mathrm{RS},&lt;}\), the corresponding prover
• in Step 7, we must simulate the implicit input \(p'\) (which is also a function from \(S\) to \(\mathbb{F}_{2^\ell}\)), and we do so as follows: for each query \(\alpha\), query \(\alpha\) to the (real) implicit input \(p\) and then return \(p(\alpha)\cdot Q(\alpha)\); note that \(Q(\alpha)\) can be evaluated in time that is \(\operatorname{poly}(\ell,\log(d_{\kappa,\eta}-d))\)
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.vLt -->
[Statement.lean, lines 903–929](../Statement.lean#L903-L929)

<pre title="Statement.lean, lines 903–929">
/-- `V_{RS,&lt;}` on `(I_ℓ, B_S, O_S, d)`, §12.3.2 (`Q_{RS,&lt;}`, `D_{RS,&lt;}`; Algorithm 15). -/
noncomputable def vLt (T : Tuple) (B : List F) (O : F) (d : ℕ) : FlatVerifier F where
  rand := randEq T B.length
  query := 2 * queryEq T B.length
  length := 2 * lengthEq T B.length
  Q := fun r i =&gt;
    let qE := queryEq T B.length
    if 1 ≤ i ∧ i ≤ qE then qEq T B O r i
    else
      -- 2. ι := i − query_{RS,=}; j′ := Q_{RS,=}(…, ι); shift proof indices by length_{RS,=}
      match qEq T B O r (i - qE) with
      | some j' =&gt; if 0 &lt; j' ∧ j' ≤ 2 ^ B.length then some j' else some (lengthEq T B.length + j')
      | none =&gt; none
  D := fun r ans =&gt;
    let qE := queryEq T B.length
    -- 3. b1 := D_{RS,=}(…, α′)
    let b1 := dEq T B O r ans
    -- 6. reset α″_i to γ_{j′}^{d_{κ,η} − d} α″_i when the i-th query of the second call is to the implicit input
    let ans2 : ℕ → F := fun i =&gt;
      match qEq T B O r i with
      | some j' =&gt;
        if 0 &lt; j' ∧ j' ≤ 2 ^ B.length then
          eltWithIndex B O j' ^ (dKE B.length T.η - d) * ans (qE + i)
        else ans (qE + i)
      | none =&gt; ans (qE + i)
    -- 7.–9. b := b1 ∧ b2
    b1 &amp;&amp; dEq T B O r ans2
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.dKE -->
[Statement.lean, lines 755–756](../Statement.lean#L755-L756)

<pre title="Statement.lean, lines 755–756">
/-- `d_{κ,η} := |S|/2^η − 1 = 2^κ/2^η − 1`. -/
def dKE (κ η : ℕ) : ℕ := 2 ^ κ / 2 ^ η - 1
</pre>
<!-- /lean -->
<p>Both recursive tests use the same initial random prefix, as printed. The source simulation of p′ is included in full; the typed flat verifier applies that transformation to the appropriate answers.</p>
</td></tr>
<tr><td>
<p><b>Algorithm 16: V_RS,=</b></p>
<p>ECCC TR12-045 revision 3, December 28, 2012; Algorithm 16, complete listing; printed p. 122; PDF p. 122. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Transcribed against the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. Printed formulas, indices and conditions are retained without repair.</i></p>

<pre>
inputs:
• \(I_\ell\), irreducible polynomial of degree \(\ell\) over \(\mathbb{F}_2\) with root \(\mathsf{x}\), inducing the field extension \(\mathbb{F}_{2^\ell}:=\mathbb{F}_2(\mathsf{x})\)
• \(\mathcal{B}_L=(a_1,\ldots,a_\kappa)\) and \(\mathcal{O}_L\), basis and offset for the \(\kappa\)-dimensional affine subset \(L\subseteq\mathbb{F}_{2^\ell}\)
randomness:
• \(r_1\cdots r_{\operatorname{rand}_{\mathrm{RS},=}(\ell,\kappa)}\)
oracles:
• \(p\), function from \(L\) to \(\mathbb{F}_{2^\ell}\)
• \(\pi=(f,\Pi)\), proof of proximity to \(\mathrm{RS}(\mathbb{F}_{2^\ell},L,|L|/2^\eta-1)\) for the function \(p\)

1. if \(\kappa\le\kappa_0\), then:
   (a) for \(i=1,\ldots,2^\kappa\):
       i. \(\alpha_i:=\operatorname{GetEltWithIndex}(I_\ell,\mathcal B_L,\mathcal O_L,i)\)
       ii. query \(\alpha_i\) to \(p\)
   (b) \(d_{\kappa,\eta}:=|L|/2^\eta-1=2^\kappa/2^\eta-1\)
   (c) \(P:=\operatorname{SubspaceInterp}(I_\ell,\mathcal B_L,\mathcal O_L,(p(\alpha_1),\ldots,p(\alpha_{2^\kappa})))\)
   (d) \(\widetilde d:=\deg(P)\)
   (e) if \(\widetilde d\le d_{\kappa,\eta}\), output \(1\), else output \(0\)
2. if \(\kappa&gt;\kappa_0\), then:
   (a) \(\mathcal B_{L_0}:=(a_1,\ldots,a_{\lfloor\kappa/2\rfloor-\gamma})\), \(\mathcal O_{L_0}:=\mathcal O_L\)
   (b) \([Z_{L_0}]^{\mathsf A}:=\operatorname{FindSubspPoly}(I_\ell,\mathcal B_{L_0},\mathcal O_{L_0})\)
   (c) \(\mathcal B_{L'_0}:=(a_1,\ldots,a_{\lfloor\kappa/2\rfloor-\gamma+\mu})\), \(\mathcal O_{L'_0}:=\mathcal O_L\)
   (d) if \(r_1=0\), then do a random row test:
       i. \(m:=1+\lceil\kappa/2\rceil+\gamma\)
       ii. \(\mathcal B_{L_1}:=(a_{\lfloor\kappa/2\rfloor-\gamma+1},\ldots,a_\kappa)\), \(\mathcal O_{L_1}:=\mathcal O_L\)
       iii. \(\beta:=\operatorname{GetRandElt}(I_\ell,\mathcal B_{L_1},\mathcal O_{L_1},(r_2,\ldots,r_{1+\lceil\kappa/2\rceil+\gamma}))\)
       iv. if \(\beta\in L'_0\), then \(\mathcal B_{L_\beta}:=(a_1,\ldots,a_{\lfloor\kappa/2\rfloor-\gamma+\mu},a_{\lfloor\kappa/2\rfloor-\gamma+\mu+1})\);
       v. if \(\beta\notin L'_0\), then \(\mathcal B_{L_\beta}:=(a_1,\ldots,a_{\lfloor\kappa/2\rfloor-\gamma+\mu},\beta+\mathcal O_{L'_0})\)
       vi. \(\mathcal O_{L_\beta}:=\mathcal O_{L'_0}\)
       vii. \(\beta':=[Z_{L_0}]^{\mathsf A}(\beta)\)
       viii. \(b:=V_{\mathrm{RS},=}^{(\widehat f|_{\beta'}^{\leftrightarrow},\pi_{\beta'}^{\leftrightarrow})}(I_\ell,\mathcal B_{L_\beta},\mathcal O_{L_\beta};r_{m+1}\cdots r_{\operatorname{rand}_{\mathrm{RS},=}(\ell,\kappa)})\)
       ix. output \(b\)
   (e) if \(r_1=1\), then do a random column test:
       i. \(m:=1+\lfloor\kappa/2\rfloor-\gamma+\mu\)
       ii. \(\alpha:=\operatorname{GetRandElt}(I_\ell,\mathcal B_{L'_0},\mathcal O_{L'_0},(r_2,\ldots,r_{1+\lfloor\kappa/2\rfloor-\gamma+\mu}))\)
       iii. \(\mathcal B_{Z_{L_0}(L_1)}:=([Z_{L_0}]^{\mathsf A}(a_{\lfloor\kappa/2\rfloor-\gamma+1})+[Z_{L_0}]^{\mathsf A}(0_{\mathbb F_{2^\ell}}),\ldots,[Z_{L_0}]^{\mathsf A}(a_\kappa)+[Z_{L_0}]^{\mathsf A}(0_{\mathbb F_{2^\ell}}))\),
            \(\mathcal O_{Z_{L_0}(L_1)}:=[Z_{L_0}]^{\mathsf A}(\mathcal O_{L_1})\)
       iv. \(b:=V_{\mathrm{RS},=}^{(\widehat f|_\alpha^{\updownarrow},\pi_\alpha^{\updownarrow})}(I_\ell,\mathcal B_{Z_{L_0}(L_1)},\mathcal O_{Z_{L_0}(L_1)};r_{m+1}\cdots r_{\operatorname{rand}_{\mathrm{RS},=}(\ell,\kappa)})\)
       v. output \(b\)

notes:
• see Theorem 11.3 for how the parameters \((\eta,\kappa_0,\gamma,\mu)\) can be chosen
• see Lemma C.1 for complexity bounds on queries and randomness
• see Lemma 12.16 for the “non-adaptive decomposition” of \(V_{\mathrm{RS},=}\) into \(Q_{\mathrm{RS},=}\) and \(D_{\mathrm{RS},=}\)
• see Algorithm 7 for \(P_{\mathrm{RS},=}\), the corresponding prover
• in Step 2(d)viii, \(\widehat f|_{\beta'}^{\leftrightarrow}\) is a function with domain \(L_\beta\times\{\beta'\}\) that is simulated as follows: for each query \(\alpha\in L_\beta\) to \(\widehat f|_{\beta'}^{\leftrightarrow}\), if \(Z_{L_0}(\alpha)=\beta'\) then return \(p(\alpha)\), else return \(f(\alpha,\beta')\)
• in Step 2(e)iv, \(\widehat f|_\alpha^{\updownarrow}\) is a function with domain \(\{\alpha\}\times Z_{L_0}(L_1)\) that is simulated as follows: for each query \(\beta'\in Z_{L_0}(L_1)\) to \(\widehat f|_\alpha^{\updownarrow}\), if \(Z_{L_0}(\alpha)=\beta'\) then return \(p(\alpha)\), else return \(f(\alpha,\beta')\)
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.vEq -->
[Statement.lean, lines 895–901](../Statement.lean#L895-L901)

<pre title="Statement.lean, lines 895–901">
/-- `V_{RS,=}` on `(I_ℓ, B_L, O_L)` (degree `|L|/2^η − 1`). -/
noncomputable def vEq (T : Tuple) (B : List F) (O : F) : FlatVerifier F where
  rand := randEq T B.length
  query := queryEq T B.length
  length := lengthEq T B.length
  Q := qEq T B O
  D := dEq T B O
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.translate -->
[Statement.lean, lines 804–848](../Statement.lean#L804-L848)

<pre title="Statement.lean, lines 804–848">
/-- `Translate(I_ℓ, B_L, O_L, r, i)` of §12.3.1 (fuel `n`). -/
def translate (T : Tuple) : ℕ → List F → F → List Bool → ℕ → TrOut F
  | 0, B, O, _, i =&gt; .inp (eltWithIndex B O i) i
  | n + 1, B, O, r, i =&gt;
    if B.length ≤ T.κ0 then
      -- 1. "αi := GetEltWithIndex(I_ℓ, B_L, O_L, i); text := implicit-input; elt := αi; output (text, elt, i)"
      .inp (eltWithIndex B O i) i
    else
      let κ := B.length
      let k := κ / 2 - T.γ                        -- dim L0
      let BL0 := B.take k                           -- (a) B_{L0} := (a_1, …, a_{⌊κ/2⌋−γ}), O_{L0} := O_L
      let BL00 := B.take (k + T.μ)                  -- (b) B_{L00} := (a_1, …, a_{⌊κ/2⌋−γ+μ}), O_{L00} := O_L
      let z : F → F := zEval BL0 O                  -- (c) [Z_{L0}]_A
      let BL1 := B.drop k                           -- B_{L1} := (a_{⌊κ/2⌋−γ+1}, …, a_κ), O_{L1} := O_L
      let nL := 2 ^ κ                               -- |L|
      let nLb := 2 ^ (k + T.μ + 1)                  -- |L_β|
      let nL1 := 2 ^ BL1.length                     -- |L1|
      if r.head? = some false then
        -- (d) row test translation
        let m := 1 + BL1.length                     -- i. m := 1 + ⌈κ/2⌉ + γ
        let β := getRandElt BL1 O ((r.drop 1).take BL1.length)   -- iii.
        let β' := z β                               -- iv.
        let ιβ := indexOfElt BL1 O β                -- v.
        let BLb := if β ∈ span BL00 O then BL00 ++ [B.getD (k + T.μ) 0] else BL00 ++ [β + O]  -- vi.–viii.
        match translate T n BLb O (r.drop m) i with  -- ix.
        | .inp α ι =&gt;                              -- x.
          if z α = β' then .inp α (indexOfElt B O α)                       -- C.
          else .prf (nL + nLb * (ιβ - 1) + ι)                               -- D.
        | .prf ι =&gt;                                 -- xi. C.
          .prf ((ι - nLb + nL) + nLb * nL1 + (ιβ - 1) * lengthEq T (k + T.μ + 1))
      else
        -- (e) column test translation
        let m := 1 + (k + T.μ)                      -- i. m := 1 + ⌊κ/2⌋ − γ + μ
        let α := getRandElt BL00 O ((r.drop 1).take (k + T.μ))   -- ii.
        let α' := z α                               -- iii.
        let ια := indexOfElt BL00 O α               -- iv.
        let BZ := BL1.map fun a =&gt; z a + z 0        -- v. B_{Z_{L0}(L1)}
        let OZ := z O                               -- vi. O_{Z_{L0}(L1)} := [Z_{L0}]_A(O_{L1})
        match translate T n BZ OZ (r.drop m) i with  -- vii.
        | .inp β' ι =&gt;                              -- viii.
          if α' = β' then .inp α (indexOfElt B O α)                         -- B.
          else .prf (nL + nLb * (ι - 1) + ια)                               -- C.
        | .prf ι =&gt;                                 -- ix. C.
          .prf ((ι - 2 ^ BZ.length + nL) + nLb * nL1 + nL1 * lengthEq T (k + T.μ + 1) +
            (ια - 1) * lengthEq T BZ.length)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.qEq -->
[Statement.lean, lines 850–854](../Statement.lean#L850-L854)

<pre title="Statement.lean, lines 850–854">
/-- `Q_{RS,=}((I_ℓ, B_L, O_L), r, i)`: "Compute (text, elt, j) := Translate(I_ℓ, B_L, O_L, r, i). Output j." -/
def qEq (T : Tuple) (B : List F) (O : F) (r : List Bool) (i : ℕ) : Option ℕ :=
  match translate T B.length B O r i with
  | .inp _ j =&gt; some j
  | .prf j =&gt; some j
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.dEq -->
[Statement.lean, lines 879–881](../Statement.lean#L879-L881)

<pre title="Statement.lean, lines 879–881">
/-- `D_{RS,=}`. -/
noncomputable def dEq (T : Tuple) (B : List F) (O : F) (r : List Bool) (ans : ℕ → F) : Bool :=
  dEqF T B.length B O r ans
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.TrOut -->
[Statement.lean, lines 799–802](../Statement.lean#L799-L802)

<pre title="Statement.lean, lines 799–802">
/-- The output of `Translate`: a query to the implicit input at a point (with its index), or to the proof. -/
inductive TrOut (F : Type) where
  | inp (α : F) (j : ℕ)
  | prf (j : ℕ)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.degreeTest -->
[Statement.lean, lines 745–749](../Statement.lean#L745-L749)

<pre title="Statement.lean, lines 745–749">
/-- The base-case test: the answers `α_1, …, α_{2^κ}` are, in GetEltWithIndex order, the values on the subspace
of a polynomial of degree at most `deg` (SubspaceInterp, then "if d̃ ≤ d, output 1, else output 0"). -/
noncomputable def degreeTest (B : List F) (O : F) (deg : ℕ) (ans : ℕ → F) : Bool :=
  @decide (∃ P : F[X], P.natDegree ≤ deg ∧ ∀ i &lt; 2 ^ B.length, P.eval (eltWithIndex B O (i + 1)) = ans (i + 1))
    (Classical.propDecidable _)
</pre>
<!-- /lean -->
<p>The full printed recursive verifier and its row/column simulations are quoted. The flat query translation and decision procedures are the non-adaptive representation described in Lemma 12.16; their indexing and fuel conventions remain explicit in the Lean declarations.</p>
</td></tr>
<tr><td>
<p><b>Field and affine-input convention</b></p>
<p>ECCC TR12-045 revision 3, December 28, 2012; §12.3.1, first sentence of the proof of Lemma 12.16, spanning printed/PDF pages 75–76; printed p. 75–76; PDF p. 75–76. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Transcribed against the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. Printed formulas, indices and conditions are retained without repair.</i></p>

<pre>
The explicit input of \(V_{\mathrm{RS},=}\) is \((I_\ell,\mathcal B_L,\mathcal O_L)\), where \(I_\ell\) is an irreducible polynomial over \(\mathbb F_2\) of degree \(\ell\) with root \(\mathsf{x}\), which induces the field extension \(\mathbb F_{2^\ell}:=\mathbb F_2(\mathsf{x})\), and \(\mathcal B_L=(a_1,\ldots,a_\kappa)\) and \(\mathcal O_L\) are the basis and the offset of a \(\kappa\)-dimensional affine subspace \(L\subseteq\mathbb F_{2^\ell}\); the implicit input of \(V_{\mathrm{RS},=}\) is a function \(p:L\to\mathbb F_{2^\ell}\).
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.FlatVerifier -->
[Statement.lean, lines 885–893](../Statement.lean#L885-L893)

<pre title="Statement.lean, lines 885–893">
/-- A verifier as §12.3 decomposes it: `rand` coins, `query` queries, proof `length` (field elements); `Q r i`
is the 1-based index of the `i`-th query into the concatenation of the implicit input (`|S|` entries) and the
proof, or `none` (`⊥`); `D r ans` decides from the answers `ans 1, ans 2, …`. -/
structure FlatVerifier (F : Type) where
  rand : ℕ
  query : ℕ
  length : ℕ
  Q : List Bool → ℕ → Option ℕ
  D : List Bool → (ℕ → F) → Bool
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.span -->
[Statement.lean, lines 723–725](../Statement.lean#L723-L725)

<pre title="Statement.lean, lines 723–725">
/-- The affine subspace with basis `B` and offset `O`: its `2^κ` points in GetEltWithIndex order. -/
def span (B : List F) (O : F) : Finset F :=
  ((List.range (2 ^ B.length)).map fun i =&gt; eltWithIndex B O (i + 1)).toFinset
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.IsBasis -->
[Statement.lean, lines 727–728](../Statement.lean#L727-L728)

<pre title="Statement.lean, lines 727–728">
/-- "`B_S` and `O_S`, basis and offset for the `κ`-dimensional affine subspace `S`": the points are distinct. -/
def IsBasis (B : List F) (O : F) : Prop := (span B O).card = 2 ^ B.length
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.vEq -->
[Statement.lean, lines 895–901](../Statement.lean#L895-L901)

<pre title="Statement.lean, lines 895–901">
/-- `V_{RS,=}` on `(I_ℓ, B_L, O_L)` (degree `|L|/2^η − 1`). -/
noncomputable def vEq (T : Tuple) (B : List F) (O : F) : FlatVerifier F where
  rand := randEq T B.length
  query := queryEq T B.length
  length := lengthEq T B.length
  Q := qEq T B O
  D := dEq T B O
</pre>
<!-- /lean -->
<p>This source sentence identifies the field, basis, offset, explicit input and implicit function. The mathematical Lean functions are stated for a characteristic-two finite field with the specified cardinality; the separate finite-field representation conventions are retained in the existing prose.</p>
</td></tr>
<tr><td>
<p><b>Vanishing-polynomial definition</b></p>
<p>ECCC TR12-045 revision 3, December 28, 2012; Lemma 11.7, defining sentence after the display of L₀ and L₁; printed p. 56; PDF p. 56. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Transcribed against the rendered published page. Mathematical typesetting is represented in TeX; line wrapping and line-break hyphenation are joined. Printed formulas, indices and conditions are retained without repair.</i></p>
<p><b>Marked omissions:</b> Only the complete defining sentence is quoted. The preceding definitions of the particular split subspaces and the subsequent conclusions/proof of Lemma 11.7 are not reproduced.</p>

<pre>
Let \(Z_{L_0}\) be the vanishing polynomial of \(L_0\), i.e., \(Z_{L_0}(x):=\prod_{\alpha\in L_0}(x-\alpha)\).
</pre>
</td><td>

<!-- lean NearCubicGates.Published.BCGT13.zEval -->
[Statement.lean, lines 730–731](../Statement.lean#L730-L731)

<pre title="Statement.lean, lines 730–731">
/-- Algorithm 21 (FindSubspPoly): the value of "the vanishing polynomial for the affine subspace S". -/
def zEval (B : List F) (O : F) (x : F) : F := ∏ s ∈ span B O, (x - s)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.BCGT13.span -->
[Statement.lean, lines 723–725](../Statement.lean#L723-L725)

<pre title="Statement.lean, lines 723–725">
/-- The affine subspace with basis `B` and offset `O`: its `2^κ` points in GetEltWithIndex order. -/
def span (B : List F) (O : F) : Finset F :=
  ((List.range (2 ^ B.length)).map fun i =&gt; eltWithIndex B O (i + 1)).toFinset
</pre>
<!-- /lean -->
<p>This is the source product definition evaluated by zEval on the affine point set. It is separate from the omitted implementation steps of Algorithm 21 and carries no imported arithmetic-circuit bound.</p>
</td></tr>
</table>
<!-- /source-table -->

<!-- source-table shoup -->
<h3>Deterministic irreducible-polynomial construction: BCGT Algorithm 17 and Shoup TR 763</h3>
<p>The release’s named field is BCGT13 Algorithm 17’s deterministic degree-only construction over F₂. Shoup’s Corollary 3.2 is checked in UW–Madison Technical Report 763, not represented as an inspection of the FOCS proceedings PDF cited by BCGT.</p>
<p>The unary positive degree, full coefficient list, constant-first order and ordinary word-machine conventions are explicit on the Lean side; they are not presented as source wording that the publications did not specify.</p>
<table>
<tr><th>Published source (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<p><b>BCGT Algorithm 17: source of the retained premise</b></p>
<p>BCGT ECCC TR12-045 revision 3, December 28, 2012; Algorithm 17 FindIrrPoly, inputs/output/step1; printed p. 124; PDF p. 124. Pinned PDF SHA-256 <code>9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0</code>.</p>
<p><i>Mathematical notation transcribed from the rendered page; superscripts/subscripts are written using ^ and _, fractions using parentheses, with typographic line wrapping normalized.</i></p>
<p><b>Marked omissions:</b> The practice-oriented notes after step1 are omitted.</p>

<pre>
Algorithm 17 FindIrrPoly
inputs:
• 1^ℓ, desired degree presented in unary
output:
• I_ℓ, irreducible polynomial of degree ℓ over F_2 with root x, inducing the field extension F_(2^ℓ) := F_2(x)
1. the algorithm of [Sho88, Corollary 3.2], which runs in time poly(ℓ)
</pre>
</td><td>
<p>Retained premise field <code>NearCubicGates.Close.PublishedInputs.shoup_findIrrPolyAlgorithm17</code>: <a href="../Statement.lean#L1832">Statement.lean, line 1832</a></p>

<pre>
  shoup_findIrrPolyAlgorithm17 : NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17
</pre>

<!-- lean NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17 -->
[Statement.lean, lines 1635–1639](../Statement.lean#L1635-L1639)

<pre title="Statement.lean, lines 1635–1639">
/-- **BCGT13 Algorithm 17 (FindIrrPoly)**, as printed: "inputs: `1^ℓ`, desired degree presented in unary; output:
`I_ℓ`, irreducible polynomial of degree `ℓ` over `F2` with root `x`, inducing the field extension `F_{2^ℓ} := F2(x)`;
1. the algorithm of [Sho88, Corollary 3.2], which runs in time `poly(ℓ)`." -/
def FindIrrPolyAlgorithm17 : Prop :=
  ∃ irrPoly : ℕ → Polynomial (ZMod 2), IrreducibleChoice irrPoly ∧ PolyTimeIrrChoice irrPoly
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.Shoup.IrreducibleChoice -->
[Statement.lean, lines 1621–1624](../Statement.lean#L1621-L1624)

<pre title="Statement.lean, lines 1621–1624">
/-- An irreducible-polynomial choice: for every `f ≥ 1`, an irreducible polynomial of degree `f` over `F2` (the
output `I_f` of `FindIrrPoly` on `1^f`, BCGT13 Algorithm 17). -/
def IrreducibleChoice (irrPoly : ℕ → (ZMod 2)[X]) : Prop :=
  ∀ f, 1 ≤ f → Irreducible (irrPoly f) ∧ (irrPoly f).natDegree = f
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.Shoup.PolyTimeIrrChoice -->
[Statement.lean, lines 1629–1633](../Statement.lean#L1629-L1633)

<pre title="Statement.lean, lines 1629–1633">
/-- BCGT13 Algorithm 17's algorithm "runs in time poly(ℓ)", read at bit level: an
ordinary machine maps `1^f` (`f ≥ 1`) to the coefficients of `irrPoly f` within `K·(f+1)^e` steps. -/
def PolyTimeIrrChoice (irrPoly : ℕ → (ZMod 2)[X]) : Prop :=
  ∃ K e : ℕ, Nonempty (NearCubicWires.RepairOrdinary.WordFunction {f : ℕ // 1 ≤ f}
    (fun f =&gt; List.replicate f.val true) (fun f =&gt; coeffWord f.val (irrPoly f.val)) (fun f =&gt; K * (f.val + 1) ^ e))
</pre>
<!-- /lean -->
<p>The publication’s adjoining root x names the field extension; the retained leaf asks only for the irreducible polynomial and its complete coefficient output, not a further computational root-finding oracle.</p>
</td></tr>
<tr><td>
<p><b>The exact Corollary 3.2 in the checked technical-report version</b></p>
<p>Shoup UW–Madison Computer Sciences TR 763, April 1, 1988 (checked report version); §3, Corollary 3.2; printed p. 8; PDF p. 9. Pinned PDF SHA-256 <code>14c05b951140d2b8996ecdac6edac7aad4c2d3a9687247b16758a421b4fee4de</code>.</p>
<p><i>Transcribed from the scanned page; mathematical superscripts/subscripts are written using ^ and _ and fractions using parentheses.</i></p>

<pre>
Corollary 3.2. We can construct an irreducible polynomial over F of degree n deterministically in time polynomial in n and p.
</pre>
</td><td>

<!-- lean NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17 -->
[Statement.lean, lines 1635–1639](../Statement.lean#L1635-L1639)

<pre title="Statement.lean, lines 1635–1639">
/-- **BCGT13 Algorithm 17 (FindIrrPoly)**, as printed: "inputs: `1^ℓ`, desired degree presented in unary; output:
`I_ℓ`, irreducible polynomial of degree `ℓ` over `F2` with root `x`, inducing the field extension `F_{2^ℓ} := F2(x)`;
1. the algorithm of [Sho88, Corollary 3.2], which runs in time `poly(ℓ)`." -/
def FindIrrPolyAlgorithm17 : Prop :=
  ∃ irrPoly : ℕ → Polynomial (ZMod 2), IrreducibleChoice irrPoly ∧ PolyTimeIrrChoice irrPoly
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.Shoup.PolyTimeIrrChoice -->
[Statement.lean, lines 1629–1633](../Statement.lean#L1629-L1633)

<pre title="Statement.lean, lines 1629–1633">
/-- BCGT13 Algorithm 17's algorithm "runs in time poly(ℓ)", read at bit level: an
ordinary machine maps `1^f` (`f ≥ 1`) to the coefficients of `irrPoly f` within `K·(f+1)^e` steps. -/
def PolyTimeIrrChoice (irrPoly : ℕ → (ZMod 2)[X]) : Prop :=
  ∃ K e : ℕ, Nonempty (NearCubicWires.RepairOrdinary.WordFunction {f : ℕ // 1 ≤ f}
    (fun f =&gt; List.replicate f.val true) (fun f =&gt; coeffWord f.val (irrPoly f.val)) (fun f =&gt; K * (f.val + 1) ^ e))
</pre>
<!-- /lean -->
<p>Fixing p=2 specializes the printed polynomial(n,p) bound to polynomial in the positive degree. This does not assert unrestricted deterministic polynomial time in log p.</p>
</td></tr>
<tr><td>
<p><b>The report’s field and positive-degree parameters</b></p>
<p>Shoup UW–Madison Computer Sciences TR 763, April 1, 1988 (checked report version); §1, opening paragraph; printed p. 2; PDF p. 3. Pinned PDF SHA-256 <code>14c05b951140d2b8996ecdac6edac7aad4c2d3a9687247b16758a421b4fee4de</code>.</p>
<p><i>Transcribed from the scanned page; mathematical superscripts/subscripts are written using ^ and _ and fractions using parentheses.</i></p>

<pre>
Let p be a prime number, F the finite field GF(p), and n a positive integer. Consider the problem of finding an irreducible polynomial in F[X] of degree n.
</pre>
</td><td>

<!-- lean NearCubicGates.Published.Shoup.IrreducibleChoice -->
[Statement.lean, lines 1621–1624](../Statement.lean#L1621-L1624)

<pre title="Statement.lean, lines 1621–1624">
/-- An irreducible-polynomial choice: for every `f ≥ 1`, an irreducible polynomial of degree `f` over `F2` (the
output `I_f` of `FindIrrPoly` on `1^f`, BCGT13 Algorithm 17). -/
def IrreducibleChoice (irrPoly : ℕ → (ZMod 2)[X]) : Prop :=
  ∀ f, 1 ≤ f → Irreducible (irrPoly f) ∧ (irrPoly f).natDegree = f
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.Shoup.coeffWord -->
[Statement.lean, lines 1626–1627](../Statement.lean#L1626-L1627)

<pre title="Statement.lean, lines 1626–1627">
/-- The `f + 1` coefficients of a polynomial of degree `f`, constant term first (FindIrrPoly's output). -/
def coeffWord (f : ℕ) (a : (ZMod 2)[X]) : List Bool := List.ofFn fun i : Fin (f + 1) =&gt; decide (a.coeff i.val = 1)
</pre>
<!-- /lean -->
<p>The coefficient-field specialization is ZMod 2. Values at degree 0 are unconstrained by the positive-degree source contract. The output ordering is a formal representation convention.</p>
</td></tr>
</table>
<!-- /source-table -->

## Complete Lean declaration closure

Every declaration of [Statement.lean](../Statement.lean) that the published statement of this page uses and that the
[main page](main-theorem.md) or an earlier input page does not already print, verbatim. `check.py` re-renders this
block and checks that the closure of the release statement is printed in full on the main page and the input
pages.

<!-- statement -->
[Statement.lean, lines 330–335](../Statement.lean#L330-L335)

<pre title="Statement.lean, lines 330–335">
structure WordFunction (Request : Type)
    (input output : Request → List Bool) (budget : Request → ℕ) where
  program : Program
  realizes : ∀ r, ∃ receipt,
    run program.machine (budget r) (program.inputTapes (input r)) = some receipt ∧
      receipt.final.tapes program.outputTape = output r
</pre>

[Statement.lean, lines 633–634](../Statement.lean#L633-L634)

<pre title="Statement.lean, lines 633–634">
/-- `⌊z/2⌋`. -/
def floorHalf (z : ℤ) : ℤ := Int.fdiv z 2
</pre>

[Statement.lean, lines 635–636](../Statement.lean#L635-L636)

<pre title="Statement.lean, lines 635–636">
/-- `⌈z/2⌉`. -/
def ceilHalf (z : ℤ) : ℤ := -Int.fdiv (-z) 2
</pre>

[Statement.lean, lines 638–639](../Statement.lean#L638-L639)

<pre title="Statement.lean, lines 638–639">
/-- `(3 + (−1)^{κ0 mod 2})/2`. -/
def sThree (κ0 : ℤ) : ℤ := Int.fdiv (3 + (-1) ^ (κ0 % 2).toNat) 2
</pre>

[Statement.lean, lines 640–641](../Statement.lean#L640-L641)

<pre title="Statement.lean, lines 640–641">
/-- `(1 + (−1)^{κ0 mod 2})/2`. -/
def sOne (κ0 : ℤ) : ℤ := Int.fdiv (1 + (-1) ^ (κ0 % 2).toNat) 2
</pre>

[Statement.lean, lines 662–672](../Statement.lean#L662-L672)

<pre title="Statement.lean, lines 662–672">
/-- Theorem 11.1, p.51: "c := (a + b/2 + √(b(b+4a))/2)^{1/min{e1,e2}}, where c0 := 4/(1 − 1/2^{η−1} −
1/2^η)², a := 2^{η+1}(1+c0)/(2^{η−1} − 1), b := 2^{μ+2}, e1 := log((κ0 + (3+(−1)^{κ0 mod 2})/2) /
(⌊(κ0 + (3+(−1)^{κ0 mod 2})/2)/2⌋ − γ + μ + 1)), e2 := log((κ0 + (1+(−1)^{κ0 mod 2})/2) /
(⌈(κ0 + (1+(−1)^{κ0 mod 2})/2)/2⌉ + γ))". -/
noncomputable def constC (η κ0 γ μ : ℤ) : ℝ :=
  let c0 : ℝ := 4 / (1 - 1 / (2 : ℝ) ^ (η - 1) - 1 / (2 : ℝ) ^ η) ^ 2
  let a : ℝ := (2 : ℝ) ^ (η + 1) * (1 + c0) / ((2 : ℝ) ^ (η - 1) - 1)
  let b : ℝ := (2 : ℝ) ^ (μ + 2)
  let e1 : ℝ := Real.logb 2 (((κ0 + sThree κ0 : ℤ) : ℝ) / ((floorHalf (κ0 + sThree κ0) - γ + μ + 1 : ℤ) : ℝ))
  let e2 : ℝ := Real.logb 2 (((κ0 + sOne κ0 : ℤ) : ℝ) / ((ceilHalf (κ0 + sOne κ0) + γ : ℤ) : ℝ))
  (a + b / 2 + Real.sqrt (b * (b + 4 * a)) / 2) ^ (1 / min e1 e2)
</pre>

[Statement.lean, lines 678–682](../Statement.lean#L678-L682)

<pre title="Statement.lean, lines 678–682">
/-- The fixed-tuple soundness term established by the BCGT13 proof after correcting the distance in
Lemma 11.10 and the balancing algebra in Corollary 11.13 (ECCC rev. 3, pp.67–68):
`K(κ) = 16·κ^{log₂ c}` at `(η, κ0, γ, μ) = (2, 4, 0, 1)`. -/
noncomputable def repairedSoundTerm (κ : ℕ) : ℝ :=
  16 * (κ : ℝ) ^ Real.logb 2 (constC 2 4 0 1)
</pre>

[Statement.lean, lines 684–689](../Statement.lean#L684-L689)

<pre title="Statement.lean, lines 684–689">
/-- A parameter tuple `(η, κ0, γ, μ)` (natural numbers). -/
structure Tuple where
  η : ℕ
  κ0 : ℕ
  γ : ℕ
  μ : ℕ
</pre>

[Statement.lean, lines 701–702](../Statement.lean#L701-L702)

<pre title="Statement.lean, lines 701–702">
/-- The tuple `(η, κ0, γ, μ) = (2, 4, 0, 1)`, the only one the release uses (`BCGT13_Theorem11_1_Fixed`). -/
def Tuple.fixed : Tuple := ⟨2, 4, 0, 1⟩
</pre>

[Statement.lean, lines 710–712](../Statement.lean#L710-L712)

<pre title="Statement.lean, lines 710–712">
/-- Algorithm 19 (GetRandElt): "α := Σ_{j=1}^κ r_j a_j + O_S" (missing bits read as 0, extra bits ignored). -/
def getRandElt (B : List F) (O : F) (r : List Bool) : F :=
  (List.zipWith (fun a b =&gt; if b then a else 0) B r).sum + O
</pre>

[Statement.lean, lines 714–717](../Statement.lean#L714-L717)

<pre title="Statement.lean, lines 714–717">
/-- Algorithm 20 (GetEltWithIndex): "α := (Σ_{j=1}^κ i_j a_j) + O_S, … i_1 ⋯ i_κ is (i − 1) in binary"
(least significant bit first, see the header). -/
def eltWithIndex (B : List F) (O : F) (i : ℕ) : F :=
  getRandElt B O ((List.range B.length).map fun j =&gt; (i - 1).testBit j)
</pre>

[Statement.lean, lines 719–721](../Statement.lean#L719-L721)

<pre title="Statement.lean, lines 719–721">
/-- GetIndexOfElt: the least `i ∈ {1, …, 2^κ}` with `GetEltWithIndex(B, O, i) = α`, and `0` if there is none. -/
def indexOfElt (B : List F) (O : F) (α : F) : ℕ :=
  (((List.range (2 ^ B.length)).find? fun i =&gt; eltWithIndex B O (i + 1) = α).map (· + 1)).getD 0
</pre>

[Statement.lean, lines 723–725](../Statement.lean#L723-L725)

<pre title="Statement.lean, lines 723–725">
/-- The affine subspace with basis `B` and offset `O`: its `2^κ` points in GetEltWithIndex order. -/
def span (B : List F) (O : F) : Finset F :=
  ((List.range (2 ^ B.length)).map fun i =&gt; eltWithIndex B O (i + 1)).toFinset
</pre>

[Statement.lean, lines 727–728](../Statement.lean#L727-L728)

<pre title="Statement.lean, lines 727–728">
/-- "`B_S` and `O_S`, basis and offset for the `κ`-dimensional affine subspace `S`": the points are distinct. -/
def IsBasis (B : List F) (O : F) : Prop := (span B O).card = 2 ^ B.length
</pre>

[Statement.lean, lines 730–731](../Statement.lean#L730-L731)

<pre title="Statement.lean, lines 730–731">
/-- Algorithm 21 (FindSubspPoly): the value of "the vanishing polynomial for the affine subspace S". -/
def zEval (B : List F) (O : F) (x : F) : F := ∏ s ∈ span B O, (x - s)
</pre>

[Statement.lean, lines 733–735](../Statement.lean#L733-L735)

<pre title="Statement.lean, lines 733–735">
/-- Def 4.7, fractional Hamming distance of functions on the evaluation set `S`. -/
noncomputable def fracDist (S : Finset F) (p q : F → F) : ℝ :=
  ((S.filter fun s =&gt; p s ≠ q s).card : ℝ) / (S.card : ℝ)
</pre>

[Statement.lean, lines 737–739](../Statement.lean#L737-L739)

<pre title="Statement.lean, lines 737–739">
/-- Def 4.3, "RS(F, S, d) := {p : S → F s.t. p is an evaluation of a polynomial of degree at most d over S}". -/
def RS (S : Finset F) (d : ℕ) : Set (F → F) :=
  {p | ∃ P : F[X], P.natDegree ≤ d ∧ ∀ s ∈ S, p s = P.eval s}
</pre>

[Statement.lean, lines 741–743](../Statement.lean#L741-L743)

<pre title="Statement.lean, lines 741–743">
/-- Def 4.4, "VRS(F, S, H, d) := {p ∈ RS(F, S, d) s.t. the polynomial corresponding to p vanishes on H}". -/
def VRS (S H : Finset F) (d : ℕ) : Set (F → F) :=
  {p | ∃ P : F[X], P.natDegree ≤ d ∧ (∀ s ∈ S, p s = P.eval s) ∧ ∀ h ∈ H, P.eval h = 0}
</pre>

[Statement.lean, lines 745–749](../Statement.lean#L745-L749)

<pre title="Statement.lean, lines 745–749">
/-- The base-case test: the answers `α_1, …, α_{2^κ}` are, in GetEltWithIndex order, the values on the subspace
of a polynomial of degree at most `deg` (SubspaceInterp, then "if d̃ ≤ d, output 1, else output 0"). -/
noncomputable def degreeTest (B : List F) (O : F) (deg : ℕ) (ans : ℕ → F) : Bool :=
  @decide (∃ P : F[X], P.natDegree ≤ deg ∧ ∀ i &lt; 2 ^ B.length, P.eval (eltWithIndex B O (i + 1)) = ans (i + 1))
    (Classical.propDecidable _)
</pre>

[Statement.lean, lines 755–756](../Statement.lean#L755-L756)

<pre title="Statement.lean, lines 755–756">
/-- `d_{κ,η} := |S|/2^η − 1 = 2^κ/2^η − 1`. -/
def dKE (κ η : ℕ) : ℕ := 2 ^ κ / 2 ^ η - 1
</pre>

[Statement.lean, lines 758–759](../Statement.lean#L758-L759)

<pre title="Statement.lean, lines 758–759">
/-- `m_{κ,η,d} := ⌊(d+1)/(d_{κ,η}+1)⌋` (Algorithm 14 step 2(b); §12.3.3). -/
def mKED (κ η d : ℕ) : ℕ := (d + 1) / (dKE κ η + 1)
</pre>

[Statement.lean, lines 761–768](../Statement.lean#L761-L768)

<pre title="Statement.lean, lines 761–768">
/-- `rand_{RS,=}(ℓ, κ)`: recursion (27) of Lemma C.9, "r(κ) = 0 if κ ≤ κ0, 1 + max{⌈κ/2⌉ + γ +
r(⌊κ/2⌋ − γ + μ + 1), ⌊κ/2⌋ − γ + μ + r(⌈κ/2⌉ + γ)} if κ &gt; κ0" (fuel `n`). -/
def randEqF (T : Tuple) : ℕ → ℕ → ℕ
  | 0, _ =&gt; 0
  | n + 1, κ =&gt;
    if κ ≤ T.κ0 then 0 else
      1 + max ((κ + 1) / 2 + T.γ + randEqF T n (κ / 2 - T.γ + T.μ + 1))
        (κ / 2 - T.γ + T.μ + randEqF T n ((κ + 1) / 2 + T.γ))
</pre>

[Statement.lean, lines 770–778](../Statement.lean#L770-L778)

<pre title="Statement.lean, lines 770–778">
/-- `length_{RS,=}(ℓ, κ)`: recursion (28) of Lemma C.10, "r(κ) = 0 if κ ≤ κ0, 2^{⌈κ/2⌉+γ}·2^{⌊κ/2⌋−γ+μ+1} +
2^{⌈κ/2⌉+γ}·r(⌊κ/2⌋ − γ + μ + 1) + 2^{⌊κ/2⌋−γ+μ}·r(⌈κ/2⌉ + γ) if κ &gt; κ0" (fuel `n`). -/
def lengthEqF (T : Tuple) : ℕ → ℕ → ℕ
  | 0, _ =&gt; 0
  | n + 1, κ =&gt;
    if κ ≤ T.κ0 then 0 else
      2 ^ ((κ + 1) / 2 + T.γ) * 2 ^ (κ / 2 - T.γ + T.μ + 1) +
        2 ^ ((κ + 1) / 2 + T.γ) * lengthEqF T n (κ / 2 - T.γ + T.μ + 1) +
        2 ^ (κ / 2 - T.γ + T.μ) * lengthEqF T n ((κ + 1) / 2 + T.γ)
</pre>

[Statement.lean, lines 780–784](../Statement.lean#L780-L784)

<pre title="Statement.lean, lines 780–784">
/-- `query_{RS,=}(ℓ, κ)`: `2^κ` base-case queries if `κ ≤ κ0`, else the larger of the two recursive calls. -/
def queryEqF (T : Tuple) : ℕ → ℕ → ℕ
  | 0, κ =&gt; 2 ^ κ
  | n + 1, κ =&gt;
    if κ ≤ T.κ0 then 2 ^ κ else max (queryEqF T n (κ / 2 - T.γ + T.μ + 1)) (queryEqF T n ((κ + 1) / 2 + T.γ))
</pre>

[Statement.lean, lines 786–787](../Statement.lean#L786-L787)

<pre title="Statement.lean, lines 786–787">
/-- `rand_{RS,=}(ℓ, κ)`. -/
def randEq (T : Tuple) (κ : ℕ) : ℕ := randEqF T κ κ
</pre>

[Statement.lean, lines 788–789](../Statement.lean#L788-L789)

<pre title="Statement.lean, lines 788–789">
/-- `length_{RS,=}(ℓ, κ)`. -/
def lengthEq (T : Tuple) (κ : ℕ) : ℕ := lengthEqF T κ κ
</pre>

[Statement.lean, lines 790–791](../Statement.lean#L790-L791)

<pre title="Statement.lean, lines 790–791">
/-- `query_{RS,=}(ℓ, κ)`. -/
def queryEq (T : Tuple) (κ : ℕ) : ℕ := queryEqF T κ κ
</pre>

[Statement.lean, lines 799–802](../Statement.lean#L799-L802)

<pre title="Statement.lean, lines 799–802">
/-- The output of `Translate`: a query to the implicit input at a point (with its index), or to the proof. -/
inductive TrOut (F : Type) where
  | inp (α : F) (j : ℕ)
  | prf (j : ℕ)
</pre>

[Statement.lean, lines 804–848](../Statement.lean#L804-L848)

<pre title="Statement.lean, lines 804–848">
/-- `Translate(I_ℓ, B_L, O_L, r, i)` of §12.3.1 (fuel `n`). -/
def translate (T : Tuple) : ℕ → List F → F → List Bool → ℕ → TrOut F
  | 0, B, O, _, i =&gt; .inp (eltWithIndex B O i) i
  | n + 1, B, O, r, i =&gt;
    if B.length ≤ T.κ0 then
      -- 1. "αi := GetEltWithIndex(I_ℓ, B_L, O_L, i); text := implicit-input; elt := αi; output (text, elt, i)"
      .inp (eltWithIndex B O i) i
    else
      let κ := B.length
      let k := κ / 2 - T.γ                        -- dim L0
      let BL0 := B.take k                           -- (a) B_{L0} := (a_1, …, a_{⌊κ/2⌋−γ}), O_{L0} := O_L
      let BL00 := B.take (k + T.μ)                  -- (b) B_{L00} := (a_1, …, a_{⌊κ/2⌋−γ+μ}), O_{L00} := O_L
      let z : F → F := zEval BL0 O                  -- (c) [Z_{L0}]_A
      let BL1 := B.drop k                           -- B_{L1} := (a_{⌊κ/2⌋−γ+1}, …, a_κ), O_{L1} := O_L
      let nL := 2 ^ κ                               -- |L|
      let nLb := 2 ^ (k + T.μ + 1)                  -- |L_β|
      let nL1 := 2 ^ BL1.length                     -- |L1|
      if r.head? = some false then
        -- (d) row test translation
        let m := 1 + BL1.length                     -- i. m := 1 + ⌈κ/2⌉ + γ
        let β := getRandElt BL1 O ((r.drop 1).take BL1.length)   -- iii.
        let β' := z β                               -- iv.
        let ιβ := indexOfElt BL1 O β                -- v.
        let BLb := if β ∈ span BL00 O then BL00 ++ [B.getD (k + T.μ) 0] else BL00 ++ [β + O]  -- vi.–viii.
        match translate T n BLb O (r.drop m) i with  -- ix.
        | .inp α ι =&gt;                              -- x.
          if z α = β' then .inp α (indexOfElt B O α)                       -- C.
          else .prf (nL + nLb * (ιβ - 1) + ι)                               -- D.
        | .prf ι =&gt;                                 -- xi. C.
          .prf ((ι - nLb + nL) + nLb * nL1 + (ιβ - 1) * lengthEq T (k + T.μ + 1))
      else
        -- (e) column test translation
        let m := 1 + (k + T.μ)                      -- i. m := 1 + ⌊κ/2⌋ − γ + μ
        let α := getRandElt BL00 O ((r.drop 1).take (k + T.μ))   -- ii.
        let α' := z α                               -- iii.
        let ια := indexOfElt BL00 O α               -- iv.
        let BZ := BL1.map fun a =&gt; z a + z 0        -- v. B_{Z_{L0}(L1)}
        let OZ := z O                               -- vi. O_{Z_{L0}(L1)} := [Z_{L0}]_A(O_{L1})
        match translate T n BZ OZ (r.drop m) i with  -- vii.
        | .inp β' ι =&gt;                              -- viii.
          if α' = β' then .inp α (indexOfElt B O α)                         -- B.
          else .prf (nL + nLb * (ι - 1) + ια)                               -- C.
        | .prf ι =&gt;                                 -- ix. C.
          .prf ((ι - 2 ^ BZ.length + nL) + nLb * nL1 + nL1 * lengthEq T (k + T.μ + 1) +
            (ια - 1) * lengthEq T BZ.length)
</pre>

[Statement.lean, lines 850–854](../Statement.lean#L850-L854)

<pre title="Statement.lean, lines 850–854">
/-- `Q_{RS,=}((I_ℓ, B_L, O_L), r, i)`: "Compute (text, elt, j) := Translate(I_ℓ, B_L, O_L, r, i). Output j." -/
def qEq (T : Tuple) (B : List F) (O : F) (r : List Bool) (i : ℕ) : Option ℕ :=
  match translate T B.length B O r i with
  | .inp _ j =&gt; some j
  | .prf j =&gt; some j
</pre>

[Statement.lean, lines 856–877](../Statement.lean#L856-L877)

<pre title="Statement.lean, lines 856–877">
/-- `D_{RS,=}((I_ℓ, B_L, O_L), r, α_1 ⋯)` of §12.3.1 (fuel `n`). -/
noncomputable def dEqF (T : Tuple) : ℕ → List F → F → List Bool → (ℕ → F) → Bool
  | 0, B, O, _, ans =&gt; degreeTest B O (dKE B.length T.η) ans
  | n + 1, B, O, r, ans =&gt;
    if B.length ≤ T.κ0 then
      -- 1. "d_{κ,η} = 2^κ/2^η − 1; P := SubspaceInterp(…); d̃ := deg(P); if d̃ ≤ d_{κ,η}, output 1, else output 0"
      degreeTest B O (dKE B.length T.η) ans
    else
      let κ := B.length
      let k := κ / 2 - T.γ
      let BL0 := B.take k
      let BL00 := B.take (k + T.μ)
      let z : F → F := zEval BL0 O
      let BL1 := B.drop k
      if r.head? = some false then
        let m := 1 + BL1.length
        let β := getRandElt BL1 O ((r.drop 1).take BL1.length)
        let BLb := if β ∈ span BL00 O then BL00 ++ [B.getD (k + T.μ) 0] else BL00 ++ [β + O]
        dEqF T n BLb O (r.drop m) ans
      else
        let m := 1 + (k + T.μ)
        dEqF T n (BL1.map fun a =&gt; z a + z 0) (z O) (r.drop m) ans
</pre>

[Statement.lean, lines 879–881](../Statement.lean#L879-L881)

<pre title="Statement.lean, lines 879–881">
/-- `D_{RS,=}`. -/
noncomputable def dEq (T : Tuple) (B : List F) (O : F) (r : List Bool) (ans : ℕ → F) : Bool :=
  dEqF T B.length B O r ans
</pre>

[Statement.lean, lines 885–893](../Statement.lean#L885-L893)

<pre title="Statement.lean, lines 885–893">
/-- A verifier as §12.3 decomposes it: `rand` coins, `query` queries, proof `length` (field elements); `Q r i`
is the 1-based index of the `i`-th query into the concatenation of the implicit input (`|S|` entries) and the
proof, or `none` (`⊥`); `D r ans` decides from the answers `ans 1, ans 2, …`. -/
structure FlatVerifier (F : Type) where
  rand : ℕ
  query : ℕ
  length : ℕ
  Q : List Bool → ℕ → Option ℕ
  D : List Bool → (ℕ → F) → Bool
</pre>

[Statement.lean, lines 895–901](../Statement.lean#L895-L901)

<pre title="Statement.lean, lines 895–901">
/-- `V_{RS,=}` on `(I_ℓ, B_L, O_L)` (degree `|L|/2^η − 1`). -/
noncomputable def vEq (T : Tuple) (B : List F) (O : F) : FlatVerifier F where
  rand := randEq T B.length
  query := queryEq T B.length
  length := lengthEq T B.length
  Q := qEq T B O
  D := dEq T B O
</pre>

[Statement.lean, lines 903–929](../Statement.lean#L903-L929)

<pre title="Statement.lean, lines 903–929">
/-- `V_{RS,&lt;}` on `(I_ℓ, B_S, O_S, d)`, §12.3.2 (`Q_{RS,&lt;}`, `D_{RS,&lt;}`; Algorithm 15). -/
noncomputable def vLt (T : Tuple) (B : List F) (O : F) (d : ℕ) : FlatVerifier F where
  rand := randEq T B.length
  query := 2 * queryEq T B.length
  length := 2 * lengthEq T B.length
  Q := fun r i =&gt;
    let qE := queryEq T B.length
    if 1 ≤ i ∧ i ≤ qE then qEq T B O r i
    else
      -- 2. ι := i − query_{RS,=}; j′ := Q_{RS,=}(…, ι); shift proof indices by length_{RS,=}
      match qEq T B O r (i - qE) with
      | some j' =&gt; if 0 &lt; j' ∧ j' ≤ 2 ^ B.length then some j' else some (lengthEq T B.length + j')
      | none =&gt; none
  D := fun r ans =&gt;
    let qE := queryEq T B.length
    -- 3. b1 := D_{RS,=}(…, α′)
    let b1 := dEq T B O r ans
    -- 6. reset α″_i to γ_{j′}^{d_{κ,η} − d} α″_i when the i-th query of the second call is to the implicit input
    let ans2 : ℕ → F := fun i =&gt;
      match qEq T B O r i with
      | some j' =&gt;
        if 0 &lt; j' ∧ j' ≤ 2 ^ B.length then
          eltWithIndex B O j' ^ (dKE B.length T.η - d) * ans (qE + i)
        else ans (qE + i)
      | none =&gt; ans (qE + i)
    -- 7.–9. b := b1 ∧ b2
    b1 &amp;&amp; dEq T B O r ans2
</pre>

[Statement.lean, lines 931–972](../Statement.lean#L931-L972)

<pre title="Statement.lean, lines 931–972">
/-- `V_{RS,&gt;}` on `(I_ℓ, B_S, O_S, d)`, §12.3.3 (`Q_{RS,&gt;}`, `D_{RS,&gt;}`; Algorithm 14), for `d &lt; 2^κ`. -/
noncomputable def vGt (T : Tuple) (B : List F) (O : F) (d : ℕ) : FlatVerifier F :=
  let κ := B.length
  let nS := 2 ^ κ
  let D' := dKE κ T.η
  let m := mKED κ T.η d                              -- (b)
  let dd := d - m * (D' + 1)                         -- (c) d_{κ,η,d}
  let one : Bool := decide (m * (D' + 1) &lt; d + 1)
  let qE := queryEq T κ
  let lE := lengthEq T κ
  let vL := vLt T B O dd
  let qL := if one then vL.query else 0
  { rand := max (max (randEq T κ) (if one then randEq T κ else 0)) κ
    query := m * qE + qL + 1 + 2 ^ T.η
    length := m * (nS + lE) + (if one then nS + vL.length else 0)
    Q := fun r i =&gt;
      if d ≥ nS then none                            -- 1. output ⊥
      else if 1 ≤ i ∧ i ≤ m * qE then                -- (d)
        let zz := (i - 1) / qE
        (qEq T B O r (i - zz * qE)).map fun j' =&gt; nS + zz * (nS + lE) + j'
      else if one ∧ 1 ≤ i - m * qE ∧ i - m * qE ≤ qL then   -- (e)
        (vL.Q r (i - m * qE)).map fun j' =&gt; nS + m * (nS + lE) + j'
      else                                            -- (f), (g): the consistency queries
        let i0 := i - (m * qE + qL)
        let γ := getRandElt B O (r.take κ)
        let ιγ := indexOfElt B O γ
        if i0 = 1 then some ιγ
        else if 1 &lt; i0 ∧ i0 ≤ m + 1 then some (nS + (i0 - 2) * (nS + lE) + ιγ)
        else if one ∧ i0 = m + 2 then some (nS + m * (nS + lE) + ιγ)
        else none
    D := fun r ans =&gt;
      if d ≥ nS then true                            -- 1. output 1
      else
        let γ := getRandElt B O (r.take κ)           -- (a), (b)
        -- ii. b_i := D_{RS,=}(…, α^{(i)}) for i &lt; m; iv. b_m := D_{RS,&lt;}(…, α^{(m)}) when 𝟏 = 1
        let bs := (List.range m).all fun z =&gt; dEq T B O r fun i =&gt; ans (z * qE + i)
        let bm := if one then vL.D r (fun i =&gt; ans (m * qE + i)) else true
        -- v. b_consist := (v = Σ_{i=0}^{2^η−1} γ^{i(d_{κ,η}+1)} v_i), with ⊥-answers 0
        let base := m * qE + qL
        let v := ans (base + 1)
        let bc := decide (v = ∑ i ∈ Finset.range (2 ^ T.η), γ ^ (i * (D' + 1)) * ans (base + 2 + i))
        bc &amp;&amp; bs &amp;&amp; bm }
</pre>

[Statement.lean, lines 974–982](../Statement.lean#L974-L982)

<pre title="Statement.lean, lines 974–982">
/-- `V_RS` on `(I_ℓ, B_S, O_S, d)`, §12.3.4 (`Q_RS`, `D_RS`; Algorithm 13): for `κ ≤ η` the direct degree test
(`Q`: "output j := i"; `D`: SubspaceInterp and "if d̃ ≤ d output 1"), otherwise `V_{RS,&lt;}`, `V_{RS,=}`, `V_{RS,&gt;}`
as `d &lt;`, `=`, `&gt; d_{κ,η}`. -/
noncomputable def vRS (T : Tuple) (B : List F) (O : F) (d : ℕ) : FlatVerifier F :=
  if B.length ≤ T.η then
    { rand := 0, query := 2 ^ B.length, length := 0, Q := fun _ i =&gt; some i, D := fun _ ans =&gt; degreeTest B O d ans }
  else if d &lt; dKE B.length T.η then vLt T B O d
  else if d = dKE B.length T.η then vEq T B O
  else vGt T B O d
</pre>

[Statement.lean, lines 984–1005](../Statement.lean#L984-L1005)

<pre title="Statement.lean, lines 984–1005">
/-- `V_VRS` on `(I_ℓ, B_S, O_S, B_H, O_H, d)`, §12.3.5 (`Q_VRS`) with the decision of Algorithm 12 (see the
header): the proof is `(p̃, π̃)`; `V_RS` tests `p̃` against degree `d − |H|`; then `p(α) = Z_H(α)·p̃(α)`. -/
noncomputable def vVRS (T : Tuple) (B : List F) (O : F) (BH : List F) (OH : F) (d : ℕ) : FlatVerifier F :=
  let κ := B.length
  let nS := 2 ^ κ
  let V := vRS T B O (d - 2 ^ BH.length)
  { rand := max V.rand κ
    query := V.query + 2
    length := nS + V.length
    Q := fun r i =&gt;
      if 1 ≤ i ∧ i ≤ V.query then (V.Q r i).map fun j =&gt; nS + j      -- 1. j := |S| + j_old
      else
        let α := getRandElt B O (r.take κ)
        if i = V.query + 1 then some (indexOfElt B O α)               -- 2. query α to p
        else if i = V.query + 2 then some (nS + indexOfElt B O α)      -- 3. query α to p̃
        else none
    D := fun r ans =&gt;
      let bRS := V.D r ans                                            -- 3. b_RS
      let α := getRandElt B O (r.take κ)                              -- 4.–5.
      let τ := zEval BH OH α                                          -- 6.–7.
      -- Algorithm 12 step 2(g): "if p(α) = ω · p̃(α), then b_consist := 1"
      bRS &amp;&amp; decide (ans (V.query + 1) = τ * ans (V.query + 2)) }
</pre>

[Statement.lean, lines 1007–1017](../Statement.lean#L1007-L1017)

<pre title="Statement.lean, lines 1007–1017">
/-- The answers to the queries of `V` on coins `r`, implicit input `p` (on `S` with basis `B`, offset `O`) and proof
`π`: index `j ∈ {1, …, |S|}` reads `p(GetEltWithIndex(B, O, j))`, index `|S| + 1 + t` reads `π t`; `⊥` and
indices out of range read `0`. -/
def FlatVerifier.answers (V : FlatVerifier F) (B : List F) (O : F) (p : F → F) (π : Fin V.length → F)
    (r : List Bool) (i : ℕ) : F :=
  match V.Q r i with
  | none =&gt; 0
  | some j =&gt;
    if 1 ≤ j ∧ j ≤ 2 ^ B.length then p (eltWithIndex B O j)
    else if h : j - 2 ^ B.length - 1 &lt; V.length ∧ 2 ^ B.length &lt; j then π ⟨j - 2 ^ B.length - 1, h.1⟩
    else 0
</pre>

[Statement.lean, lines 1019–1022](../Statement.lean#L1019-L1022)

<pre title="Statement.lean, lines 1019–1022">
/-- `V^{(p,π)}(x; r)`. -/
def FlatVerifier.accepts (V : FlatVerifier F) (B : List F) (O : F) (p : F → F) (π : Fin V.length → F)
    (r : Fin V.rand → Bool) : Bool :=
  V.D (List.ofFn r) (V.answers B O p π (List.ofFn r))
</pre>

[Statement.lean, lines 1024–1027](../Statement.lean#L1024-L1027)

<pre title="Statement.lean, lines 1024–1027">
/-- `Pr_R[V^{(p,π)}(x; R) = 1]` for uniform `R ∈ {0,1}^rand`. -/
noncomputable def FlatVerifier.acceptProb (V : FlatVerifier F) (B : List F) (O : F) (p : F → F)
    (π : Fin V.length → F) : ℝ :=
  ((univ.filter fun r =&gt; V.accepts B O p π r = true).card : ℝ) / (2 : ℝ) ^ V.rand
</pre>

[Statement.lean, lines 1065–1087](../Statement.lean#L1065-L1087)

<pre title="Statement.lean, lines 1065–1087">
/-- **BCGT13 Theorem 11.1 at `(η, κ0, γ, μ) = (2, 4, 0, 1)`, with a weaker proof bound:** using
`1−2^{1−η}` for the distance in Lemma 11.10 and the product obtained from Corollary 11.13's τ algebra
(rather than the printed sum) gives `K(κ) = 16·κ^{log₂ c}`, RS denominator `1+K` and VRS denominator
`2+K` (ECCC rev. 3, pp.67–69).
The verifiers, constant `c`, completeness, degree ranges and all other quantifiers are unchanged, and
`bcgt13Fixed_of_theorem11_1` proves that the recorded printed statement implies this fixed release input. -/
def BCGT13_Theorem11_1_Fixed : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (ℓ : ℕ), Fintype.card F = 2 ^ ℓ →
  ∀ (B : List F) (O : F), IsBasis B O →
    -- V_RS on explicit input (I_ℓ, B_S, O_S, d), "d, positive integer indicating what “low-degree” means"
    -- (Algorithm 13 inputs, p.119; §12.3.4, p.82: "… and d is a positive integer")
    (∀ d : ℕ, 1 ≤ d → d &lt; 2 ^ B.length →
      (∀ p ∈ RS (span B O) d, ∃ π, ∀ r, (vRS Tuple.fixed B O d).accepts B O p π r = true) ∧
      ∀ (p : F → F) (π : Fin (vRS Tuple.fixed B O d).length → F) (δ : ℝ),
        (∀ q ∈ RS (span B O) d, δ ≤ fracDist (span B O) p q) →
        (vRS Tuple.fixed B O d).acceptProb B O p π ≤ 1 - δ / (1 + repairedSoundTerm B.length)) ∧
    -- V_VRS on explicit input (I_ℓ, B_S, O_S, B_H, O_H, d)
    (∀ (BH : List F) (OH : F), IsBasis BH OH → span BH OH ⊆ span B O →
     ∀ d : ℕ, 2 ^ BH.length ≤ d → d &lt; 2 ^ B.length →
      (∀ p ∈ VRS (span B O) (span BH OH) d, ∃ π, ∀ r, (vVRS Tuple.fixed B O BH OH d).accepts B O p π r = true) ∧
      ∀ (p : F → F) (π : Fin (vVRS Tuple.fixed B O BH OH d).length → F) (δ : ℝ),
        (∀ q ∈ VRS (span B O) (span BH OH) d, δ ≤ fracDist (span B O) p q) →
        (vVRS Tuple.fixed B O BH OH d).acceptProb B O p π ≤ 1 - δ / (2 + repairedSoundTerm B.length))
</pre>

[Statement.lean, lines 1621–1624](../Statement.lean#L1621-L1624)

<pre title="Statement.lean, lines 1621–1624">
/-- An irreducible-polynomial choice: for every `f ≥ 1`, an irreducible polynomial of degree `f` over `F2` (the
output `I_f` of `FindIrrPoly` on `1^f`, BCGT13 Algorithm 17). -/
def IrreducibleChoice (irrPoly : ℕ → (ZMod 2)[X]) : Prop :=
  ∀ f, 1 ≤ f → Irreducible (irrPoly f) ∧ (irrPoly f).natDegree = f
</pre>

[Statement.lean, lines 1626–1627](../Statement.lean#L1626-L1627)

<pre title="Statement.lean, lines 1626–1627">
/-- The `f + 1` coefficients of a polynomial of degree `f`, constant term first (FindIrrPoly's output). -/
def coeffWord (f : ℕ) (a : (ZMod 2)[X]) : List Bool := List.ofFn fun i : Fin (f + 1) =&gt; decide (a.coeff i.val = 1)
</pre>

[Statement.lean, lines 1629–1633](../Statement.lean#L1629-L1633)

<pre title="Statement.lean, lines 1629–1633">
/-- BCGT13 Algorithm 17's algorithm "runs in time poly(ℓ)", read at bit level: an
ordinary machine maps `1^f` (`f ≥ 1`) to the coefficients of `irrPoly f` within `K·(f+1)^e` steps. -/
def PolyTimeIrrChoice (irrPoly : ℕ → (ZMod 2)[X]) : Prop :=
  ∃ K e : ℕ, Nonempty (NearCubicWires.RepairOrdinary.WordFunction {f : ℕ // 1 ≤ f}
    (fun f =&gt; List.replicate f.val true) (fun f =&gt; coeffWord f.val (irrPoly f.val)) (fun f =&gt; K * (f.val + 1) ^ e))
</pre>

[Statement.lean, lines 1635–1639](../Statement.lean#L1635-L1639)

<pre title="Statement.lean, lines 1635–1639">
/-- **BCGT13 Algorithm 17 (FindIrrPoly)**, as printed: "inputs: `1^ℓ`, desired degree presented in unary; output:
`I_ℓ`, irreducible polynomial of degree `ℓ` over `F2` with root `x`, inducing the field extension `F_{2^ℓ} := F2(x)`;
1. the algorithm of [Sho88, Corollary 3.2], which runs in time `poly(ℓ)`." -/
def FindIrrPolyAlgorithm17 : Prop :=
  ∃ irrPoly : ℕ → Polynomial (ZMod 2), IrreducibleChoice irrPoly ∧ PolyTimeIrrChoice irrPoly
</pre>
<!-- /statement -->
