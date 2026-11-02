# 9. Three-query proximity and an efficient linear encoder

[Mapping index](README.md) · derived field `threeQueryPCPP` · two published premises

[`Assembly.field9Encoder`](../SourceAdapters/Assembly/Field9Encoder.lean) proves
`PerfectThreeQueryProximityLiteral ∧ EfficientLinearEncoder`. Its premises are exactly
`NearCubicGates.Published.CW19Proximity.Lemma22Half` and `NearCubicGates.Published.CW19Code.Lemma26` in
[Statement.lean](../Statement.lean). Lemmas 24 and 27 describe derived constructions; they are not the retained
source leaves.

Source: L. Chen and R. R. Williams, *Stronger Connections Between Circuit Analysis and Circuit Lower Bounds, via
PCPs of Proximity*, CCC 2019, LIPIcs 137, article 19,
[doi:10.4230/LIPIcs.CCC.2019.19](https://doi.org/10.4230/LIPIcs.CCC.2019.19). Definition 20 and Lemma 22 are on
printed p.19:15, Lemma 26 on p.19:16, and the nonadaptive address/decision construction is in Appendix A,
pp.19:38–19:39. Pinned PDF SHA-256:
`c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533`.

## Source proximity and its conversion

At each fixed rational proximity η in (0,1), `Lemma22Half` supplies a constant query bound, logarithmic
randomness, perfect completeness, soundness at most 1/2 and a uniform polynomial-time honest-proof algorithm.
Input coordinates and proof addresses are distinct. Addresses and the decision predicate depend on the circuit
and coins, not on answers. The four polynomial-time clauses of the retained statement (the number of coins, the
number of queries, the query addresses and the decision predicate) use the polynomial-time verifier convention
of Ben-Sasson, Goldreich, Harsha, Sudan and Vadhan (BGHSV06), Definition 2.1, cited as [11] by CW19. That
definition requires polynomial-time generation of the queries and decision circuit. CW19's Definition 20 does
not itself state a verifier running time; these efficiency clauses are traced to its cited verifier definition.
The source's far condition is **strict**: distance from every accepted input exceeds
η. The source statement does not assume a table of three-literal clauses or the final dense proof-address codec.

[`Proximity.perfect_three_query_proximity`](../SourceAdapters/Proximity/Perfect.lean) proves the target
three-query interface. Clause conversion, enumeration of the bounded random strings, sorting and removing unused
proof addresses, restriction of the honest proof, output serialization and the required machine conversions are
proved. The target's non-strict distance boundary is handled by choosing a smaller source proximity; equality at
the target threshold is not silently attributed to the source. The polynomial proof-length bound follows from
the constructed finite schedule of queried addresses, not an extra assumed proof-length guarantee.

## Source code and its conversion

`Lemma26` supplies one constant-rate binary linear code family beyond an onset, a fixed positive minimum
relative distance, an efficient encoder and a promised decoder. The ordinary encoder reads the message; the
decoder reads unary message length, a separator and the received word. Both algorithms and their polynomial
constants are fixed before all messages. The decoder's termination and correctness are required only near a
codeword. A source decoding radius may be decreased to obtain the closed promised radius in the formal
statement; no total behavior outside that promise is assumed.

[`Code.efficientLinearCode_of_lemma26`](../SourceAdapters/Code/Source.lean) proves the stronger
`EfficientLinearCodeLiteral`: the three-block construction, parity supports of size at most half the message
length, constant rate, positive distance, a closed target decoding radius, total decoding, finite-length patches
and both polynomial-time machine witnesses. Totalization uses a bounded run, with proved cost, and a default output. It does
not replace the promised source decoder by an unproved total-decoder hypothesis.

The main theorem needs only the encoder part of that result. `Assembly.encoder_of_code` projects it to
`EfficientLinearEncoder`; `field9Encoder` combines it with the three-query proximity theorem. In the
[gadget reduction](../Proof/Gates/Gadget/ThreeQuery.lean), the verifier tests the relation y = (x,Enc(x)) with
D(x)=1. For a rejected x, any accepted pair has a different prefix, so code distance gives proximity soundness.
For an accepted x, perfect completeness and the honest proof apply. This systematic relation never calls the
decoder. The current [paper](../paper/near-cubic-gates-v3.tex) labels are `imp:three-pcpp` and `sec:gadget-transfer`.

Check separately the strict source proximity, the target distance boundary, uniform honest-proof construction,
the promised source decoder, the proved total decoder and the final encoder-only consumer. Conflating these
interfaces would hide precisely the conversions the adapters establish.

## Published sources beside the retained Lean statements

The tables repeat selected mathematical declarations for direct comparison. Source quotations and explicitly marked mathematical or scan transcriptions carry their exact source versions and locators. The complete generated Lean declaration closure is retained below.

<!-- source-table cw-proximity -->
<h3>CW19 Lemma 22 at soundness 1/2</h3>
<p>The retained premise field is NearCubicGates.Close.PublishedInputs.cw19Proximity_lemma22Half. The Lean column is generated verbatim from Statement.lean.</p>
<p>The source quantifies over real constants δ and s; the retained statement specializes soundness to 1/2 and uses each fixed rational η ∈ (0,1). Appendix A explicitly uses the s=1/2 instance.</p>
<p>CW19 Definition 20 does not itself state a verifier running time. The polynomial-time verifier convention is Definition 2.1 of its cited reference [11], BGHSV06; the pinned full version is January 2006 and is not the SIAM typeset PDF.</p>
<p>The flat node-list circuit encoding, finite proof extension by false, separate input/proof address tags, request tuple encodings, framed input tape, ordinary bit-multitape model and polynomial budget conventions are formal representation choices. The source quotations do not purport to specify these bytes.</p>
<p>All mathematical notation in manually transcribed quotes was checked against rendered primary PDF pages. Source wording is retained, including the printed phrase “making V(C) always accepts” in Lemma 22. Decorative heading/bullet glyphs and physical line wraps are not copied.</p>
<table>
<tr><th>Published source (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<p><b>Published premise: Lemma 22</b></p>
<p>CCC 2019, LIPIcs 137, article 19, published Dagstuhl version; Lemma 22 (Theorem 3.3 in [11]); printed p. 19:15; PDF p. 15. Pinned PDF SHA-256 <code>c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533</code>.</p>
<p><i>Verbatim wording, with mathematical notation transcribed into LaTeX after checking the rendered PDF; physical line wrapping normalized. The source PDF has a text layer and is not a scan. The statement body is quoted; its heading is identified by the locator.</i></p>

<pre>
For any constants \(0 &lt; \delta, s &lt; 1\), there is a PCP of proximity system for Circuit-Eval with proximity \(\delta\), soundness \(s\), number of random bits \(r = O(\log n)\) and query complexity \(q = O(1)\). Moreover, given the pair \((C,w) \in \text{Circuit-Eval}\), a proof \(\pi\) making \(V(C)\) always accepts can be constructed in \(\operatorname{poly}(|C| + |w|)\) time.
</pre>
</td><td>
<p>Retained premise field <code>NearCubicGates.Close.PublishedInputs.cw19Proximity_lemma22Half</code>: <a href="../Statement.lean#L1834">Statement.lean, line 1834</a></p>

<pre>
  cw19Proximity_lemma22Half : NearCubicGates.Published.CW19Proximity.Lemma22Half
</pre>

<!-- lean NearCubicGates.Published.CW19Proximity.Lemma22Half -->
[Statement.lean, lines 1359–1385](../Statement.lean#L1359-L1385)

<pre title="Statement.lean, lines 1359–1385">
/-- Lemma 22: "For any constants 0 &lt; δ, s &lt; 1, there is a PCP of
proximity system for Circuit-Eval with proximity δ, soundness s, number of
random bits r = O(log n) and query complexity q = O(1). Moreover, given the
pair (C, w) ∈ Circuit-Eval, a proof π making V (C) always accepts can be
constructed in poly(|C| + |w|) time."

Only the instance s=1/2 used in Appendix A is imported. Uniform query and
decision procedures are explicit. The finite proof length is unconstrained;
its polynomial trimmed replacement is proved, not assumed. `clog (L+2)` is
the total small-length convention for O(log L), with the constant existential. -/
def Lemma22Half : Prop :=
  ∀ eta : ℚ, 0 &lt; eta → eta &lt; 1 →
    ∃ q : ℕ, ∃ V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q,
    ∃ proofLength : SourceCircuit → ℕ,
      (∀ C coins j address, (V C).query coins j = .inr address → address &lt; proofLength C) ∧
      (∃ a : ℕ, ∀ C, (V C).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord C).length + 2)) ∧
      SourcePolyTime sourceCircuitWord (fun C =&gt; (V C).randomBits.bits) ∧
      SourcePolyTime (coinRequestWord (V := V)) (fun p =&gt; ((V p.1).queryCount p.2).bits) ∧
      SourcePolyTime (queryRequestWord (V := V))
        (fun p =&gt; queryAddressWord ((V p.1).query p.2.1 p.2.2)) ∧
      SourcePolyTime (decisionRequestWord (V := V))
        (fun p =&gt; [(V p.1).decision p.2.1 p.2.2]) ∧
      (∀ C input, StrictlyFar eta C input → ∀ proof : BitInput (proofLength C),
        (V C).fraction input (finiteProofOracle proof) ≤ (1 / 2 : ℝ)) ∧
      ∃ honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1),
        (∀ p coins, (V p.1).accepts p.2.val (finiteProofOracle (honest p)) coins = true) ∧
        SourcePolyTime acceptedSourceWord (fun p =&gt; List.ofFn (honest p))
</pre>
<!-- /lean -->
<p>The retained premise field is printed beside its exact statement. The source lemma has arbitrary constant soundness; the right side retains its 1/2 instance.</p>
</td></tr>
<tr><td>
<p><b>The pair language Circuit-Eval</b></p>
<p>CCC 2019, LIPIcs 137, article 19, published Dagstuhl version; Section 2, Preliminaries, first sentence; printed p. 19:13; PDF p. 13. Pinned PDF SHA-256 <code>c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533</code>.</p>
<p><i>Verbatim wording, with mathematical notation transcribed into LaTeX after checking the rendered PDF; physical line wrapping normalized. The source PDF has a text layer and is not a scan. The statement body is quoted; its heading is identified by the locator.</i></p>

<pre>
The Circuit Evaluation Problem (Circuit-Eval) is the language of pairs \(\{(C,w)\}\) such that when \(C\) is a general fan-in-2 circuit and \(w\) is a Boolean input, \((C,w) \in \text{Circuit-Eval}\) if and only if \(C(w) = 1\).
</pre>
</td><td>

<!-- lean NearCubicWires.BooleanNode -->
[Statement.lean, lines 105–114](../Statement.lean#L105-L114)

<pre title="Statement.lean, lines 105–114">
/-- One node in a topologically ordered fan-in-two Boolean DAG.  Child
references are natural-number node addresses; `BooleanCircuit.wellFormed`
requires every child to precede the node that uses it. -/
inductive BooleanNode (n : ℕ) where
  | const (value : Bool)
  | input (index : Fin n)
  | not (child : ℕ)
  | and (left right : ℕ)
  | or (left right : ℕ)
  deriving Repr
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.BooleanNode.WellFormedAt -->
[Statement.lean, lines 116–122](../Statement.lean#L116-L122)

<pre title="Statement.lean, lines 116–122">
def BooleanNode.WellFormedAt {n : ℕ} (index : ℕ) :
    BooleanNode n → Prop
  | .const _ =&gt; True
  | .input _ =&gt; True
  | .not child =&gt; child &lt; index
  | .and left right =&gt; left &lt; index ∧ right &lt; index
  | .or left right =&gt; left &lt; index ∧ right &lt; index
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.BooleanNode.eval -->
[Statement.lean, lines 124–132](../Statement.lean#L124-L132)

<pre title="Statement.lean, lines 124–132">
def BooleanNode.eval {n : ℕ} (input : BitInput n)
    (prior : Array Bool) : BooleanNode n → Bool
  | .const value =&gt; value
  | .input index =&gt; input index
  | .not child =&gt; !(prior[child]?.getD false)
  | .and left right =&gt;
      prior[left]?.getD false &amp;&amp; prior[right]?.getD false
  | .or left right =&gt;
      prior[left]?.getD false || prior[right]?.getD false
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.BooleanCircuit -->
[Statement.lean, lines 134–143](../Statement.lean#L134-L143)

<pre title="Statement.lean, lines 134–143">
/-- General Boolean circuits (fan-in-two AND and OR, NOT, constants and inputs): finite DAGs with a topological
node order. Their size counts DAG nodes, so a shared subcircuit counts once (it is not the size of the unfolded
formula); see `BooleanCircuit.size`. -/
structure BooleanCircuit (n : ℕ) where
  nodes : List (BooleanNode n)
  output : Fin nodes.length
  wellFormed :
    ∀ index : Fin nodes.length,
      (nodes.get index).WellFormedAt index.val
  deriving Repr
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.BooleanCircuit.values -->
[Statement.lean, lines 145–148](../Statement.lean#L145-L148)

<pre title="Statement.lean, lines 145–148">
def BooleanCircuit.values {n : ℕ} (circuit : BooleanCircuit n)
    (input : BitInput n) : Array Bool :=
  circuit.nodes.foldl
    (fun prior node =&gt; prior.push (node.eval input prior)) #[]
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.BooleanCircuit.eval -->
[Statement.lean, lines 150–152](../Statement.lean#L150-L152)

<pre title="Statement.lean, lines 150–152">
def BooleanCircuit.eval {n : ℕ} (circuit : BooleanCircuit n)
    (input : BitInput n) : Bool :=
  (circuit.values input)[circuit.output.val]?.getD false
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.BooleanCircuit.size -->
[Statement.lean, lines 154–156](../Statement.lean#L154-L156)

<pre title="Statement.lean, lines 154–156">
/-- The number of nodes, input and constant nodes included (the circuit's vertex count). -/
def BooleanCircuit.size {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  circuit.nodes.length
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.SourceCircuit -->
[Statement.lean, lines 1243–1249](../Statement.lean#L1243-L1249)

<pre title="Statement.lean, lines 1243–1249">
/-- Section 2 (preliminaries): "when C is a general fan-in-2 circuit and w is a Boolean
input, (C, w) ∈ Circuit-Eval if and only if C(w) = 1." Input vertices count
toward size; the source description below is a flat topological node list. -/
structure SourceCircuit where
  arity : ℕ
  circuit : BooleanCircuit arity
  inputs_le_size : arity ≤ circuit.size
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.sourceNodeWord -->
[Statement.lean, lines 1251–1258](../Statement.lean#L1251-L1258)

<pre title="Statement.lean, lines 1251–1258">
/-- Lemma 22: "poly(|C| + |w|) time." Representation convention for |C|:
three-bit node tags and self-delimited binary references in a flat node list. -/
def sourceNodeWord {n : ℕ} : BooleanNode n → List Bool
  | .const b =&gt; [false, false, false, b]
  | .input i =&gt; [false, false, true] ++ RepairOrdinary.frame i.val.bits
  | .not i =&gt; [false, true, false] ++ RepairOrdinary.frame i.bits
  | .and i j =&gt; [false, true, true] ++ RepairOrdinary.frame i.bits ++ RepairOrdinary.frame j.bits
  | .or i j =&gt; [true, false, false] ++ RepairOrdinary.frame i.bits ++ RepairOrdinary.frame j.bits
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.sourceCircuitWord -->
[Statement.lean, lines 1260–1266](../Statement.lean#L1260-L1266)

<pre title="Statement.lean, lines 1260–1266">
/-- Lemma 22: "poly(|C| + |w|) time." This explicit conventional source word
contains arity, node count, output index, then the flat node records. -/
def sourceCircuitWord (C : SourceCircuit) : List Bool :=
  RepairOrdinary.frame C.arity.bits ++
    RepairOrdinary.frame C.circuit.nodes.length.bits ++
    RepairOrdinary.frame C.circuit.output.val.bits ++
    C.circuit.nodes.flatMap sourceNodeWord
</pre>
<!-- /lean -->
<p>The source fixes general fan-in-two circuits. The right side chooses an explicit finite topological DAG and an ordinary binary source encoding; those representation details are conventions, not extra quoted words.</p>
</td></tr>
<tr><td>
<p><b>Definition of PCP of proximity</b></p>
<p>CCC 2019, LIPIcs 137, article 19, published Dagstuhl version; Definition 20 (Probabilistic Checkable Proofs of Proximity (PCP of proximity, or PCPP)); printed p. 19:15; PDF p. 15. Pinned PDF SHA-256 <code>c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533</code>.</p>
<p><i>Verbatim wording, with mathematical notation transcribed into LaTeX after checking the rendered PDF; physical line wrapping normalized. The source PDF has a text layer and is not a scan. The statement body is quoted; its heading is identified by the locator.</i></p>

<pre>
For \(s,\delta : \mathbb{N} \to [0,1]\) and \(r,q : \mathbb{N} \to \mathbb{N}\), a verifier \(V\) is a PCP of proximity system for a pair language \(L\) with proximity parameter \(\delta\), soundness parameter \(s\), number of random bits \(r\) and query complexity \(q\) if the following holds for all \(x,y\):

If \((x,y) \in L\), there is a proof \(\pi\) such that \(V(x)\) accepts oracle \(y \circ \pi\) with probability 1.

If \(y\) is \(\delta(|x|)\)-far from \(L(x) := \{z : (x,z) \in L\}\), then for all proofs \(\pi\), \(V(x)\) accepts oracle \(y \circ \pi\) with probability at most \(s(|x|)\).

\(V(x)\) tosses \(r(|x|)\) random coins, and makes at most \(q(|x|)\) non-adaptive queries.
</pre>
</td><td>

<!-- lean NearCubicGates.Published.CW19Proximity.QueryAddress -->
[Statement.lean, lines 1275–1277](../Statement.lean#L1275-L1277)

<pre title="Statement.lean, lines 1275–1277">
/-- Definition 20: "V (x) tosses r(|x|) random coins, and makes at most q(|x|)
non-adaptive queries." Input and proof positions are kept separate. -/
abbrev QueryAddress (n : ℕ) := Fin n ⊕ ℕ
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.oracleValue -->
[Statement.lean, lines 1279–1282](../Statement.lean#L1279-L1282)

<pre title="Statement.lean, lines 1279–1282">
/-- Definition 20: "accepts oracle y ◦ π". -/
def oracleValue {n : ℕ} (input : BitInput n) (proof : ℕ → Bool)
    (address : QueryAddress n) : Bool :=
  Sum.elim input proof address
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.NonadaptiveVerifier.fraction -->
[Statement.lean, lines 1298–1302](../Statement.lean#L1298-L1302)

<pre title="Statement.lean, lines 1298–1302">
/-- Definition 20: "accepts oracle y ◦ π with probability at most s(|x|)." -/
noncomputable def NonadaptiveVerifier.fraction {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) : ℝ :=
  ((Finset.univ.filter fun coins =&gt; V.accepts input proof coins = true).card : ℝ) /
    (2 ^ V.randomBits : ℝ)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.finiteProofOracle -->
[Statement.lean, lines 1304–1307](../Statement.lean#L1304-L1307)

<pre title="Statement.lean, lines 1304–1307">
/-- Definition 20: "there is a proof π". A finite proof has zero values
outside its domain; every queried address is required to lie in its domain. -/
def finiteProofOracle {length : ℕ} (proof : BitInput length) : ℕ → Bool :=
  fun address =&gt; if h : address &lt; length then proof ⟨address, h⟩ else false
</pre>
<!-- /lean -->
<p>The source uses the concatenated oracle y ∘ π. The direct-sum addresses and false extension outside a finite proof are explicit representation conventions.</p>
</td></tr>
<tr><td>
<p><b>Strict source distance boundary</b></p>
<p>CCC 2019, LIPIcs 137, article 19, published Dagstuhl version; Introduction, Error Correcting Codes and Probabilistic Checkable Proofs of Proximity, clarification sentence; printed p. 19:11; PDF p. 11. Pinned PDF SHA-256 <code>c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533</code>.</p>
<p><i>Verbatim wording, with mathematical notation transcribed into LaTeX after checking the rendered PDF; physical line wrapping normalized. The source PDF has a text layer and is not a scan. The statement body is quoted; its heading is identified by the locator.</i></p>

<pre>
To clarify the second point, we are saying that if \(x\) has hamming distance more than \(\delta n\) from all \(y\) that satisfy \(E\), then \(V(E)\) has decent probability of rejection on any proof \(\pi\).
</pre>
<p>January 2006 author full version; not the SIAM typeset version; Section 2, Notation, relative distance paragraph (first three sentences); printed p. 10; PDF p. 11. Pinned PDF SHA-256 <code>ff46a605d18cd6b3443239574edd8d2e9073cd8b49a32d41c989f72ac44f6ee1</code>.</p>
<p><i>Verbatim wording, with mathematical notation transcribed into LaTeX after checking the rendered PDF; physical line wrapping normalized. The source PDF has a text layer and is not a scan. The statement body is quoted; its heading is identified by the locator.</i></p>
<p><b>Marked omissions:</b> The rest of the paragraph, starting with the sentence about absolute Hamming distance and ending with repetition notation, is not included. The displayed quotation is one contiguous excerpt.</p>

<pre>
We will extensively refer to the relative distance between strings/sequences over some alphabet \(\Sigma\): For \(u,v \in \Sigma^\ell\), we denote by \(\Delta(u,v)\) the fraction of locations on which \(u\) and \(v\) differ (i.e., \(\Delta(u,v) \triangleq |\{i : u_i \ne v_i\}|/\ell\), where \(u = u_1 \cdots u_\ell \in \Sigma^\ell\) and \(v = v_1 \cdots v_\ell \in \Sigma^\ell\)). We say that \(u\) is \(\delta\)-close to \(v\) (resp., \(\delta\)-far from \(v\)) if \(\Delta(u,v) \le \delta\) (resp., \(\Delta(u,v) &gt; \delta\)). The relative distance of a string to a set of strings is defined in the natural manner; that is, \(\Delta(u,S) \triangleq \min_{v \in S}\{\Delta(u,v)\}\).
</pre>
</td><td>

<!-- lean NearCubicGates.PublishedSources.PCPP.relativeHamming -->
[Statement.lean, lines 544–545](../Statement.lean#L544-L545)

<pre title="Statement.lean, lines 544–545">
noncomputable def relativeHamming {n : ℕ} (x y : BitInput n) : ℝ :=
  ((Finset.univ.filter fun i =&gt; x i ≠ y i).card : ℝ) / n
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.StrictlyFar -->
[Statement.lean, lines 1354–1357](../Statement.lean#L1354-L1357)

<pre title="Statement.lean, lines 1354–1357">
/-- Source p.19:11: "hamming distance more than δn from all y that satisfy E". -/
def StrictlyFar (eta : ℚ) (C : SourceCircuit) (input : BitInput C.arity) : Prop :=
  ∀ accepted : BitInput C.arity, C.circuit.eval accepted = true →
    (eta : ℝ) &lt; PublishedSources.PCPP.relativeHamming input accepted
</pre>
<!-- /lean -->
<p>CW19 explicitly says more than δn. The adjacent BGHSV06 definition makes the normalized strict inequality and distance-to-set notation explicit. The target closed boundary is established later by an adapter.</p>
</td></tr>
<tr><td>
<p><b>Nonadaptive query addresses and decision predicate</b></p>
<p>CCC 2019, LIPIcs 137, article 19, published Dagstuhl version; Appendix A, proof of Lemma 24, first two paragraphs; printed p. 19:38; PDF p. 38. Pinned PDF SHA-256 <code>c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533</code>.</p>
<p><i>Verbatim wording, with mathematical notation transcribed into LaTeX after checking the rendered PDF; physical line wrapping normalized. The source PDF has a text layer and is not a scan. The statement body is quoted; its heading is identified by the locator.</i></p>

<pre>
By Lemma 22, there is a PCP of proximity system \(V\) for Circuit-Eval with proximity \(\delta\), soundness \(s = 1/2\), number of random bits \(r = O(\log n)\) and query complexity \(q = O_\delta(1)\).

Let the circuit be \(C\). Suppose we are given random bits \(R \in \{0,1\}^r\), so that \(V(C)\) queries positions \(k_1 = k_1(C,R), k_2 = k_2(C,R), \ldots, k_q = k_q(C,R)\) of the oracle \(z = w \circ \pi\), computes a predicate \(P = P(C,R)\) on these bits, and outputs \(P(z_{k_1},z_{k_2},\ldots,z_{k_q})\).
</pre>
</td><td>

<!-- lean NearCubicGates.Published.CW19Proximity.NonadaptiveVerifier -->
[Statement.lean, lines 1284–1291](../Statement.lean#L1284-L1291)

<pre title="Statement.lean, lines 1284–1291">
/-- Appendix A: "computes a predicate P = P (C, R) on these bits, and outputs
P (zk1 , zk2 , . . . , zkq )." The maps see coins but no oracle answers. -/
structure NonadaptiveVerifier (n q : ℕ) where
  randomBits : ℕ
  queryCount : Fin (2 ^ randomBits) → ℕ
  queryCount_le : ∀ coins, queryCount coins ≤ q
  query : (coins : Fin (2 ^ randomBits)) → Fin (queryCount coins) → QueryAddress n
  decision : (coins : Fin (2 ^ randomBits)) → BitInput (queryCount coins) → Bool
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.NonadaptiveVerifier.accepts -->
[Statement.lean, lines 1293–1296](../Statement.lean#L1293-L1296)

<pre title="Statement.lean, lines 1293–1296">
/-- Appendix A: "outputs P (zk1 , zk2 , . . . , zkq )." -/
def NonadaptiveVerifier.accepts {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (coins : Fin (2 ^ V.randomBits)) : Bool :=
  V.decision coins (fun j =&gt; oracleValue input proof (V.query coins j))
</pre>
<!-- /lean -->
<p>This is the source verifier V before the derived three-query conversion. Query positions and decision depend on C and R, not on oracle answers. The source paragraph is in the proof of Lemma 24 but describes the Lemma 22 verifier.</p>
</td></tr>
<tr><td>
<p><b>The cited polynomial-time verifier convention</b></p>
<p>January 2006 author full version; not the SIAM typeset version; Definition 2.1 (PCP verifiers), both bullets; printed p. 10; PDF p. 11. Pinned PDF SHA-256 <code>ff46a605d18cd6b3443239574edd8d2e9073cd8b49a32d41c989f72ac44f6ee1</code>.</p>
<p><i>Verbatim wording, with mathematical notation transcribed into LaTeX after checking the rendered PDF; physical line wrapping normalized. The source PDF has a text layer and is not a scan. The statement body is quoted; its heading is identified by the locator.</i></p>

<pre>
A verifier is a probabilistic polynomial-time algorithm \(V\) that, on an input \(x\) of length \(n\), tosses \(r = r(n)\) random coins \(R\) and generates a sequence of \(q = q(n)\) queries \(I = (i_1,\ldots,i_q)\) and a circuit \(D : \{0,1\}^q \to \{0,1\}\) of size at most \(d(n)\).

We think of \(V\) as representing a probabilistic oracle machine that queries its oracle \(\pi\) for the positions in \(I\), receives the \(q\) answer bits \(\pi|_I \triangleq (\pi_{i_1},\ldots,\pi_{i_q})\), and accepts iff \(D(\pi|_I) = 1\).

We write \((I,D) \overset{R}{\leftarrow} V(x)\) to denote the queries and circuit generated by \(V\) on input \(x\) and random coin tosses, and \((I,D) = V(x;R)\) if we wish to specify the coin tosses \(R\).
</pre>
</td><td>

<!-- lean NearCubicGates.Published.CW19Proximity.SourcePolyTime -->
[Statement.lean, lines 1268–1273](../Statement.lean#L1268-L1273)

<pre title="Statement.lean, lines 1268–1273">
/-- Lemma 22: "can be constructed in poly(|C| + |w|) time." Ordinary
polynomial time means an actual finite-control bit-multitape computation on
the stated source words, with constants chosen after the proximity. -/
def SourcePolyTime {Request : Type} (input output : Request → List Bool) : Prop :=
  ∃ K e : ℕ, Nonempty (RepairOrdinary.WordFunction Request input output
    (fun request =&gt; K * ((input request).length + 1) ^ e))
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.queryAddressWord -->
[Statement.lean, lines 1309–1313](../Statement.lean#L1309-L1313)

<pre title="Statement.lean, lines 1309–1313">
/-- Definition 20: "non-adaptive queries." The bit tag separates input from
proof addresses; both addresses use ordinary self-delimited binary notation. -/
def queryAddressWord {n : ℕ} : QueryAddress n → List Bool
  | .inl i =&gt; false :: RepairOrdinary.frame i.val.bits
  | .inr address =&gt; true :: RepairOrdinary.frame address.bits
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.CoinRequest -->
[Statement.lean, lines 1315–1317](../Statement.lean#L1315-L1317)

<pre title="Statement.lean, lines 1315–1317">
/-- Definition 20: "V (x) tosses r(|x|) random coins". -/
abbrev CoinRequest {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :=
  Σ C : SourceCircuit, Fin (2 ^ (V C).randomBits)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.coinRequestWord -->
[Statement.lean, lines 1319–1323](../Statement.lean#L1319-L1323)

<pre title="Statement.lean, lines 1319–1323">
/-- Definition 20: "makes at most q(|x|) non-adaptive queries". The source
query procedure reports its actual query count before any oracle answers. -/
def coinRequestWord {q : ℕ} {V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q}
    (p : CoinRequest V) : List Bool :=
  sourceCircuitWord p.1 ++ RepairOrdinary.frame p.2.val.bits
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.QueryRequest -->
[Statement.lean, lines 1325–1327](../Statement.lean#L1325-L1327)

<pre title="Statement.lean, lines 1325–1327">
/-- Appendix A: "positions k1 = k1 (C, R), k2 = k2 (C, R), ...". -/
abbrev QueryRequest {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :=
  Σ C : SourceCircuit, Σ coins : Fin (2 ^ (V C).randomBits), Fin ((V C).queryCount coins)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.queryRequestWord -->
[Statement.lean, lines 1329–1334](../Statement.lean#L1329-L1334)

<pre title="Statement.lean, lines 1329–1334">
/-- Appendix A: "positions k1 = k1 (C, R), k2 = k2 (C, R), ...".
The input promise only restricts the supplied coin and query indices. -/
def queryRequestWord {q : ℕ} {V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q}
    (p : QueryRequest V) : List Bool :=
  sourceCircuitWord p.1 ++ RepairOrdinary.frame p.2.1.val.bits ++
    RepairOrdinary.frame p.2.2.val.bits
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.DecisionRequest -->
[Statement.lean, lines 1336–1338](../Statement.lean#L1336-L1338)

<pre title="Statement.lean, lines 1336–1338">
/-- Appendix A: "computes a predicate P = P (C, R) on these bits". -/
abbrev DecisionRequest {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :=
  Σ C : SourceCircuit, Σ coins : Fin (2 ^ (V C).randomBits), BitInput ((V C).queryCount coins)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.decisionRequestWord -->
[Statement.lean, lines 1340–1343](../Statement.lean#L1340-L1343)

<pre title="Statement.lean, lines 1340–1343">
/-- Appendix A: "computes a predicate P = P (C, R) on these bits". -/
def decisionRequestWord {q : ℕ} {V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q}
    (p : DecisionRequest V) : List Bool :=
  sourceCircuitWord p.1 ++ RepairOrdinary.frame p.2.1.val.bits ++ List.ofFn p.2.2
</pre>
<!-- /lean -->
<p>CW19 reference [11] is identified on printed page 19:35, PDF page 35. BGHSV06 Definition 2.1 is printed page 10, PDF page 11. The concrete request/output encodings on the right are conventions implementing this verifier notion.</p>
</td></tr>
<tr><td>
<p><b>Uniform construction on accepted inputs</b></p>
<p>CCC 2019, LIPIcs 137, article 19, published Dagstuhl version; Lemma 22, moreover sentence; printed p. 19:15; PDF p. 15. Pinned PDF SHA-256 <code>c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533</code>.</p>
<p><i>Verbatim wording, with mathematical notation transcribed into LaTeX after checking the rendered PDF; physical line wrapping normalized. The source PDF has a text layer and is not a scan. The statement body is quoted; its heading is identified by the locator.</i></p>

<pre>
Moreover, given the pair \((C,w) \in \text{Circuit-Eval}\), a proof \(\pi\) making \(V(C)\) always accepts can be constructed in \(\operatorname{poly}(|C| + |w|)\) time.
</pre>
<p>CCC 2019, LIPIcs 137, article 19, published Dagstuhl version; Remark 23; printed p. 19:15; PDF p. 15. Pinned PDF SHA-256 <code>c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533</code>.</p>

<pre>
The moreover part is not explicitly stated in [11], but it is evident from the constructions.
</pre>
</td><td>

<!-- lean NearCubicGates.Published.CW19Proximity.AcceptedSourceInput -->
[Statement.lean, lines 1345–1347](../Statement.lean#L1345-L1347)

<pre title="Statement.lean, lines 1345–1347">
/-- Lemma 22: "given the pair (C, w) ∈ Circuit-Eval". -/
abbrev AcceptedSourceInput := Σ C : SourceCircuit,
  {input : BitInput C.arity // C.circuit.eval input = true}
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Proximity.acceptedSourceWord -->
[Statement.lean, lines 1349–1352](../Statement.lean#L1349-L1352)

<pre title="Statement.lean, lines 1349–1352">
/-- Lemma 22: "given the pair (C, w) ∈ Circuit-Eval". This is a promise,
not an instruction for the honest algorithm to test circuit acceptance. -/
def acceptedSourceWord (p : AcceptedSourceInput) : List Bool :=
  sourceCircuitWord p.1 ++ List.ofFn p.2.val
</pre>
<!-- /lean -->
<p>The accepted source input is a promise. The quotation does not require the honest-proof algorithm to decide circuit acceptance. Remark 23 is retained so the relationship to the cited older construction remains explicit.</p>
</td></tr>
</table>
<!-- /source-table -->

<!-- source-table cw-code -->
<h3>CW19 Lemma 26: the source linear code</h3>
<p>The retained premise field is NearCubicGates.Close.PublishedInputs.cw19Code_lemma26. The Lean column is generated verbatim from Statement.lean.</p>
<p>CW19 Lemma 26 is the retained source statement. Lemma 27 supplies a derived modification and is not an additional retained premise. The Section 4 quotation only records the paper's explicit binary encoder/decoder and constant-rate notation; it refers to Lemma 27, and is not the statement of Lemma 26.</p>
<p>CW19 does not expand a separate formal definition of linearity, code family, encoder input format or decoder input format. The right side uses Boolean vectors, zero/XOR linearity, an onset for constant rate, one ordinary machine per algorithm, and an explicit unary-length decoder request. These are representation/convention notes, not verbatim source definitions.</p>
<p>The source decoder is used only under its near-codeword promise. The formal closed source radius may be chosen smaller; total decoding and three-block sparse-support construction are later proved adapters and are not imported here.</p>
<table>
<tr><th>Published source (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<p><b>Published premise: Lemma 26</b></p>
<p>CCC 2019, LIPIcs 137, article 19, published Dagstuhl version; Section 2.4, Lemma 26 ([43]); printed p. 19:16; PDF p. 16. Pinned PDF SHA-256 <code>c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533</code>.</p>
<p><i>Verbatim wording, with mathematical notation transcribed into LaTeX after checking the rendered PDF; physical line wrapping normalized. The source PDF has a text layer and is not a scan. The statement body is quoted; its heading is identified by the locator.</i></p>

<pre>
There is a constant \(\delta &gt; 0\) such that there is a constant-rate linear error correcting code ECC with minimum relative distance \(\delta\), an efficient encoder Enc and an efficient decoder Dec recovering error up to \(c_1 \cdot \delta\), where \(c_1\) is a universal constant.
</pre>
</td><td>
<p>Retained premise field <code>NearCubicGates.Close.PublishedInputs.cw19Code_lemma26</code>: <a href="../Statement.lean#L1835">Statement.lean, line 1835</a></p>

<pre>
  cw19Code_lemma26 : NearCubicGates.Published.CW19Code.Lemma26
</pre>

<!-- lean NearCubicGates.Published.CW19Code.Lemma26 -->
[Statement.lean, lines 1185–1198](../Statement.lean#L1185-L1198)

<pre title="Statement.lean, lines 1185–1198">
/-- "There is a constant δ &gt; 0 such that there is a constant-rate linear
error correcting code ECC with minimum relative distance δ, an efficient encoder Enc and an
efficient decoder Dec recovering error up to c1 · δ, where c1 is a universal constant."

Literal source ingredients only; the three-block construction of Lemma 27 is
deliberately absent. All constants and programs are independent of the input. -/
def Lemma26 : Prop :=
  ∃ (F : BinaryFamily) (distance fraction : ℝ) (onset rate : ℕ),
    0 &lt; distance ∧ 0 &lt; fraction ∧
    IsLinear F ∧
    (∀ n, onset ≤ n → F.length n ≤ rate * n) ∧
    MinimumDistance F onset distance ∧
    Nonempty (EfficientEncoder F onset) ∧
    Nonempty (PromisedDecoder F onset (fraction * distance))
</pre>
<!-- /lean -->
<p>The exact source statement does not contain the three-block modification or the n/2 support bound of Lemma 27.</p>
</td></tr>
<tr><td>
<p><b>Binary family and rate notation used in the paper</b></p>
<p>CCC 2019, LIPIcs 137, article 19, published Dagstuhl version; Section 4, proof of Theorem 5, paragraph beginning Let δ₁; printed p. 19:20; PDF p. 20. Pinned PDF SHA-256 <code>c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533</code>.</p>
<p><i>Verbatim wording, with mathematical notation transcribed into LaTeX after checking the rendered PDF; physical line wrapping normalized. The source PDF has a text layer and is not a scan. The statement body is quoted; its heading is identified by the locator.</i></p>

<pre>
Let \(\delta_1 &gt; 0\) be the constant of Lemma 27. We fix a constant-rate linear error correcting code with minimum relative distance \(\delta_1\), as guaranteed by Lemma 27. Let \(\operatorname{Enc} : \{0,1\}^n \to \{0,1\}^{cn}\) and \(\operatorname{Dec} : \{0,1\}^{cn} \to \{0,1\}^n\) be the corresponding encoder and decoder, where \(c \ge 1\) is a constant corresponding to the rate of the code. Let \(\delta_{\mathrm{Dec}} = c_1 \cdot \delta_1\), which is error rate that Dec can recover.
</pre>
</td><td>

<!-- lean NearCubicGates.Published.CW19Code.BinaryFamily -->
[Statement.lean, lines 1138–1142](../Statement.lean#L1138-L1142)

<pre title="Statement.lean, lines 1138–1142">
/-- "a constant-rate linear error correcting code ECC" (Lemma 26).
The underlying code family, before any source properties are imposed. -/
structure BinaryFamily where
  length : ℕ → ℕ
  encode : (n : ℕ) → BitInput n → BitInput (length n)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Code.IsLinear -->
[Statement.lean, lines 1144–1150](../Statement.lean#L1144-L1150)

<pre title="Statement.lean, lines 1144–1150">
/-- "linear error correcting code ECC" (Lemma 26).
The two vector-space identities for a binary linear map. -/
def IsLinear (F : BinaryFamily) : Prop :=
  (∀ n, F.encode n (fun _ =&gt; false) = fun _ =&gt; false) ∧
  ∀ n (x y : BitInput n),
    F.encode n (fun i =&gt; xor (x i) (y i)) =
      fun j =&gt; xor (F.encode n x j) (F.encode n y j)
</pre>
<!-- /lean -->
<p>This source usage paragraph explicitly invokes Lemma 27. It is included for the binary Enc/Dec domains and constant-rate notation only. Zero/XOR identities and the variable-length family type are formal conventions for the word linear; they are not separately printed by CW19.</p>
</td></tr>
<tr><td>
<p><b>Minimum relative distance</b></p>
<p>CCC 2019, LIPIcs 137, article 19, published Dagstuhl version; Lemma 26, contiguous phrase; printed p. 19:16; PDF p. 16. Pinned PDF SHA-256 <code>c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533</code>.</p>
<p><i>Verbatim wording, with mathematical notation transcribed into LaTeX after checking the rendered PDF; physical line wrapping normalized. The source PDF has a text layer and is not a scan. The statement body is quoted; its heading is identified by the locator.</i></p>
<p><b>Marked omissions:</b> Contiguous phrase from the middle of Lemma 26; the complete statement is quoted in the first row of this table.</p>

<pre>
a constant-rate linear error correcting code ECC with minimum relative distance \(\delta\)
</pre>
<p>January 2006 author full version; not the SIAM typeset version; Section 2, Notation, definition of relative distance; printed p. 10; PDF p. 11. Pinned PDF SHA-256 <code>ff46a605d18cd6b3443239574edd8d2e9073cd8b49a32d41c989f72ac44f6ee1</code>.</p>
<p><i>Verbatim wording, with mathematical notation transcribed into LaTeX after checking the rendered PDF; physical line wrapping normalized. The source PDF has a text layer and is not a scan. The statement body is quoted; its heading is identified by the locator.</i></p>
<p><b>Marked omissions:</b> The paragraph prefix before For and later sentences about closeness, sets, absolute distance and repetition are not included. The quotation is one contiguous excerpt.</p>

<pre>
For \(u,v \in \Sigma^\ell\), we denote by \(\Delta(u,v)\) the fraction of locations on which \(u\) and \(v\) differ (i.e., \(\Delta(u,v) \triangleq |\{i : u_i \ne v_i\}|/\ell\), where \(u = u_1 \cdots u_\ell \in \Sigma^\ell\) and \(v = v_1 \cdots v_\ell \in \Sigma^\ell\)).
</pre>
</td><td>

<!-- lean NearCubicGates.Published.CW19Code.MinimumDistance -->
[Statement.lean, lines 1152–1155](../Statement.lean#L1152-L1155)

<pre title="Statement.lean, lines 1152–1155">
/-- "minimum relative distance δ" (Lemma 26). -/
def MinimumDistance (F : BinaryFamily) (onset : ℕ) (distance : ℝ) : Prop :=
  ∀ n, onset ≤ n → ∀ x y : BitInput n, x ≠ y →
    distance ≤ relativeHamming (F.encode n x) (F.encode n y)
</pre>
<!-- /lean -->
<p>The source phrase is in the first-row statement. Relative Hamming distance is a fraction of unequal coordinates; the normalized distance definition is the same common notation used by the paper's PCPP reference BGHSV06. The actual relativeHamming declaration is printed with the proximity definition row above.</p>
</td></tr>
<tr><td>
<p><b>Efficient encoder and promised decoder</b></p>
<p>CCC 2019, LIPIcs 137, article 19, published Dagstuhl version; Lemma 26, final contiguous phrase; printed p. 19:16; PDF p. 16. Pinned PDF SHA-256 <code>c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533</code>.</p>
<p><i>Verbatim wording, with mathematical notation transcribed into LaTeX after checking the rendered PDF; physical line wrapping normalized. The source PDF has a text layer and is not a scan. The statement body is quoted; its heading is identified by the locator.</i></p>
<p><b>Marked omissions:</b> Contiguous final phrase from Lemma 26; the beginning is quoted in the first row of this table.</p>

<pre>
an efficient encoder Enc and an efficient decoder Dec recovering error up to \(c_1 \cdot \delta\), where \(c_1\) is a universal constant.
</pre>
</td><td>

<!-- lean NearCubicGates.Published.CW19Code.EfficientEncoder -->
[Statement.lean, lines 1162–1171](../Statement.lean#L1162-L1171)

<pre title="Statement.lean, lines 1162–1171">
/-- "an efficient encoder Enc" (Lemma 26).
An ordinary program, with one polynomial bound for all source lengths. -/
structure EfficientEncoder (F : BinaryFamily) (onset : ℕ) where
  program : Program
  coefficient : ℕ
  exponent : ℕ
  encodes : ∀ n, onset ≤ n → ∀ x : BitInput n, ∃ receipt,
    run program.machine (coefficient * (n + 1) ^ exponent)
      (program.inputTapes (List.ofFn x)) = some receipt ∧
    receipt.final.tapes program.outputTape = List.ofFn (F.encode n x)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Code.PromisedDecoder -->
[Statement.lean, lines 1173–1183](../Statement.lean#L1173-L1183)

<pre title="Statement.lean, lines 1173–1183">
/-- "an efficient decoder Dec recovering error up to c1 · δ" (Lemma 26).
This promised-time program has no asserted behavior on unpromised inputs. -/
structure PromisedDecoder (F : BinaryFamily) (onset : ℕ) (radius : ℝ) where
  program : Program
  coefficient : ℕ
  exponent : ℕ
  decodes : ∀ n, onset ≤ n → ∀ (x : BitInput n) (y : BitInput (F.length n)),
    relativeHamming (F.encode n x) y ≤ radius → ∃ receipt,
      run program.machine (coefficient * (n + F.length n + 1) ^ exponent)
        (program.inputTapes (decoderInput F n y)) = some receipt ∧
      receipt.final.tapes program.outputTape = List.ofFn x
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Published.CW19Code.decoderInput -->
[Statement.lean, lines 1157–1160](../Statement.lean#L1157-L1160)

<pre title="Statement.lean, lines 1157–1160">
/-- Unary source description of the decoder's message length and received word.
This is a representation convention, not an additional published claim. -/
def decoderInput (F : BinaryFamily) (n : ℕ) (y : BitInput (F.length n)) : List Bool :=
  List.replicate n true ++ false :: List.ofFn y
</pre>
<!-- /lean -->
<p>The exact tape programs, polynomial witnesses, unary message-length separator, fresh output tape and closed promised radius are the explicit formal conventions and specialization stated in the existing prose. The source does not specify these encodings or behavior outside the decoding promise.</p>
</td></tr>
</table>
<!-- /source-table -->

## Complete Lean declaration closure

Every declaration of [Statement.lean](../Statement.lean) that the published statement of this page uses and that the
[main page](main-theorem.md) or an earlier input page does not already print, verbatim. `check.py` re-renders this
block and checks that the closure of the release statement is printed in full on the main page and the input
pages.

<!-- statement -->
[Statement.lean, lines 105–114](../Statement.lean#L105-L114)

<pre title="Statement.lean, lines 105–114">
/-- One node in a topologically ordered fan-in-two Boolean DAG.  Child
references are natural-number node addresses; `BooleanCircuit.wellFormed`
requires every child to precede the node that uses it. -/
inductive BooleanNode (n : ℕ) where
  | const (value : Bool)
  | input (index : Fin n)
  | not (child : ℕ)
  | and (left right : ℕ)
  | or (left right : ℕ)
  deriving Repr
</pre>

[Statement.lean, lines 116–122](../Statement.lean#L116-L122)

<pre title="Statement.lean, lines 116–122">
def BooleanNode.WellFormedAt {n : ℕ} (index : ℕ) :
    BooleanNode n → Prop
  | .const _ =&gt; True
  | .input _ =&gt; True
  | .not child =&gt; child &lt; index
  | .and left right =&gt; left &lt; index ∧ right &lt; index
  | .or left right =&gt; left &lt; index ∧ right &lt; index
</pre>

[Statement.lean, lines 124–132](../Statement.lean#L124-L132)

<pre title="Statement.lean, lines 124–132">
def BooleanNode.eval {n : ℕ} (input : BitInput n)
    (prior : Array Bool) : BooleanNode n → Bool
  | .const value =&gt; value
  | .input index =&gt; input index
  | .not child =&gt; !(prior[child]?.getD false)
  | .and left right =&gt;
      prior[left]?.getD false &amp;&amp; prior[right]?.getD false
  | .or left right =&gt;
      prior[left]?.getD false || prior[right]?.getD false
</pre>

[Statement.lean, lines 134–143](../Statement.lean#L134-L143)

<pre title="Statement.lean, lines 134–143">
/-- General Boolean circuits (fan-in-two AND and OR, NOT, constants and inputs): finite DAGs with a topological
node order. Their size counts DAG nodes, so a shared subcircuit counts once (it is not the size of the unfolded
formula); see `BooleanCircuit.size`. -/
structure BooleanCircuit (n : ℕ) where
  nodes : List (BooleanNode n)
  output : Fin nodes.length
  wellFormed :
    ∀ index : Fin nodes.length,
      (nodes.get index).WellFormedAt index.val
  deriving Repr
</pre>

[Statement.lean, lines 145–148](../Statement.lean#L145-L148)

<pre title="Statement.lean, lines 145–148">
def BooleanCircuit.values {n : ℕ} (circuit : BooleanCircuit n)
    (input : BitInput n) : Array Bool :=
  circuit.nodes.foldl
    (fun prior node =&gt; prior.push (node.eval input prior)) #[]
</pre>

[Statement.lean, lines 150–152](../Statement.lean#L150-L152)

<pre title="Statement.lean, lines 150–152">
def BooleanCircuit.eval {n : ℕ} (circuit : BooleanCircuit n)
    (input : BitInput n) : Bool :=
  (circuit.values input)[circuit.output.val]?.getD false
</pre>

[Statement.lean, lines 154–156](../Statement.lean#L154-L156)

<pre title="Statement.lean, lines 154–156">
/-- The number of nodes, input and constant nodes included (the circuit's vertex count). -/
def BooleanCircuit.size {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  circuit.nodes.length
</pre>

[Statement.lean, lines 544–545](../Statement.lean#L544-L545)

<pre title="Statement.lean, lines 544–545">
noncomputable def relativeHamming {n : ℕ} (x y : BitInput n) : ℝ :=
  ((Finset.univ.filter fun i =&gt; x i ≠ y i).card : ℝ) / n
</pre>

[Statement.lean, lines 1138–1142](../Statement.lean#L1138-L1142)

<pre title="Statement.lean, lines 1138–1142">
/-- "a constant-rate linear error correcting code ECC" (Lemma 26).
The underlying code family, before any source properties are imposed. -/
structure BinaryFamily where
  length : ℕ → ℕ
  encode : (n : ℕ) → BitInput n → BitInput (length n)
</pre>

[Statement.lean, lines 1144–1150](../Statement.lean#L1144-L1150)

<pre title="Statement.lean, lines 1144–1150">
/-- "linear error correcting code ECC" (Lemma 26).
The two vector-space identities for a binary linear map. -/
def IsLinear (F : BinaryFamily) : Prop :=
  (∀ n, F.encode n (fun _ =&gt; false) = fun _ =&gt; false) ∧
  ∀ n (x y : BitInput n),
    F.encode n (fun i =&gt; xor (x i) (y i)) =
      fun j =&gt; xor (F.encode n x j) (F.encode n y j)
</pre>

[Statement.lean, lines 1152–1155](../Statement.lean#L1152-L1155)

<pre title="Statement.lean, lines 1152–1155">
/-- "minimum relative distance δ" (Lemma 26). -/
def MinimumDistance (F : BinaryFamily) (onset : ℕ) (distance : ℝ) : Prop :=
  ∀ n, onset ≤ n → ∀ x y : BitInput n, x ≠ y →
    distance ≤ relativeHamming (F.encode n x) (F.encode n y)
</pre>

[Statement.lean, lines 1157–1160](../Statement.lean#L1157-L1160)

<pre title="Statement.lean, lines 1157–1160">
/-- Unary source description of the decoder's message length and received word.
This is a representation convention, not an additional published claim. -/
def decoderInput (F : BinaryFamily) (n : ℕ) (y : BitInput (F.length n)) : List Bool :=
  List.replicate n true ++ false :: List.ofFn y
</pre>

[Statement.lean, lines 1162–1171](../Statement.lean#L1162-L1171)

<pre title="Statement.lean, lines 1162–1171">
/-- "an efficient encoder Enc" (Lemma 26).
An ordinary program, with one polynomial bound for all source lengths. -/
structure EfficientEncoder (F : BinaryFamily) (onset : ℕ) where
  program : Program
  coefficient : ℕ
  exponent : ℕ
  encodes : ∀ n, onset ≤ n → ∀ x : BitInput n, ∃ receipt,
    run program.machine (coefficient * (n + 1) ^ exponent)
      (program.inputTapes (List.ofFn x)) = some receipt ∧
    receipt.final.tapes program.outputTape = List.ofFn (F.encode n x)
</pre>

[Statement.lean, lines 1173–1183](../Statement.lean#L1173-L1183)

<pre title="Statement.lean, lines 1173–1183">
/-- "an efficient decoder Dec recovering error up to c1 · δ" (Lemma 26).
This promised-time program has no asserted behavior on unpromised inputs. -/
structure PromisedDecoder (F : BinaryFamily) (onset : ℕ) (radius : ℝ) where
  program : Program
  coefficient : ℕ
  exponent : ℕ
  decodes : ∀ n, onset ≤ n → ∀ (x : BitInput n) (y : BitInput (F.length n)),
    relativeHamming (F.encode n x) y ≤ radius → ∃ receipt,
      run program.machine (coefficient * (n + F.length n + 1) ^ exponent)
        (program.inputTapes (decoderInput F n y)) = some receipt ∧
      receipt.final.tapes program.outputTape = List.ofFn x
</pre>

[Statement.lean, lines 1185–1198](../Statement.lean#L1185-L1198)

<pre title="Statement.lean, lines 1185–1198">
/-- "There is a constant δ &gt; 0 such that there is a constant-rate linear
error correcting code ECC with minimum relative distance δ, an efficient encoder Enc and an
efficient decoder Dec recovering error up to c1 · δ, where c1 is a universal constant."

Literal source ingredients only; the three-block construction of Lemma 27 is
deliberately absent. All constants and programs are independent of the input. -/
def Lemma26 : Prop :=
  ∃ (F : BinaryFamily) (distance fraction : ℝ) (onset rate : ℕ),
    0 &lt; distance ∧ 0 &lt; fraction ∧
    IsLinear F ∧
    (∀ n, onset ≤ n → F.length n ≤ rate * n) ∧
    MinimumDistance F onset distance ∧
    Nonempty (EfficientEncoder F onset) ∧
    Nonempty (PromisedDecoder F onset (fraction * distance))
</pre>

[Statement.lean, lines 1243–1249](../Statement.lean#L1243-L1249)

<pre title="Statement.lean, lines 1243–1249">
/-- Section 2 (preliminaries): "when C is a general fan-in-2 circuit and w is a Boolean
input, (C, w) ∈ Circuit-Eval if and only if C(w) = 1." Input vertices count
toward size; the source description below is a flat topological node list. -/
structure SourceCircuit where
  arity : ℕ
  circuit : BooleanCircuit arity
  inputs_le_size : arity ≤ circuit.size
</pre>

[Statement.lean, lines 1251–1258](../Statement.lean#L1251-L1258)

<pre title="Statement.lean, lines 1251–1258">
/-- Lemma 22: "poly(|C| + |w|) time." Representation convention for |C|:
three-bit node tags and self-delimited binary references in a flat node list. -/
def sourceNodeWord {n : ℕ} : BooleanNode n → List Bool
  | .const b =&gt; [false, false, false, b]
  | .input i =&gt; [false, false, true] ++ RepairOrdinary.frame i.val.bits
  | .not i =&gt; [false, true, false] ++ RepairOrdinary.frame i.bits
  | .and i j =&gt; [false, true, true] ++ RepairOrdinary.frame i.bits ++ RepairOrdinary.frame j.bits
  | .or i j =&gt; [true, false, false] ++ RepairOrdinary.frame i.bits ++ RepairOrdinary.frame j.bits
</pre>

[Statement.lean, lines 1260–1266](../Statement.lean#L1260-L1266)

<pre title="Statement.lean, lines 1260–1266">
/-- Lemma 22: "poly(|C| + |w|) time." This explicit conventional source word
contains arity, node count, output index, then the flat node records. -/
def sourceCircuitWord (C : SourceCircuit) : List Bool :=
  RepairOrdinary.frame C.arity.bits ++
    RepairOrdinary.frame C.circuit.nodes.length.bits ++
    RepairOrdinary.frame C.circuit.output.val.bits ++
    C.circuit.nodes.flatMap sourceNodeWord
</pre>

[Statement.lean, lines 1268–1273](../Statement.lean#L1268-L1273)

<pre title="Statement.lean, lines 1268–1273">
/-- Lemma 22: "can be constructed in poly(|C| + |w|) time." Ordinary
polynomial time means an actual finite-control bit-multitape computation on
the stated source words, with constants chosen after the proximity. -/
def SourcePolyTime {Request : Type} (input output : Request → List Bool) : Prop :=
  ∃ K e : ℕ, Nonempty (RepairOrdinary.WordFunction Request input output
    (fun request =&gt; K * ((input request).length + 1) ^ e))
</pre>

[Statement.lean, lines 1275–1277](../Statement.lean#L1275-L1277)

<pre title="Statement.lean, lines 1275–1277">
/-- Definition 20: "V (x) tosses r(|x|) random coins, and makes at most q(|x|)
non-adaptive queries." Input and proof positions are kept separate. -/
abbrev QueryAddress (n : ℕ) := Fin n ⊕ ℕ
</pre>

[Statement.lean, lines 1279–1282](../Statement.lean#L1279-L1282)

<pre title="Statement.lean, lines 1279–1282">
/-- Definition 20: "accepts oracle y ◦ π". -/
def oracleValue {n : ℕ} (input : BitInput n) (proof : ℕ → Bool)
    (address : QueryAddress n) : Bool :=
  Sum.elim input proof address
</pre>

[Statement.lean, lines 1284–1291](../Statement.lean#L1284-L1291)

<pre title="Statement.lean, lines 1284–1291">
/-- Appendix A: "computes a predicate P = P (C, R) on these bits, and outputs
P (zk1 , zk2 , . . . , zkq )." The maps see coins but no oracle answers. -/
structure NonadaptiveVerifier (n q : ℕ) where
  randomBits : ℕ
  queryCount : Fin (2 ^ randomBits) → ℕ
  queryCount_le : ∀ coins, queryCount coins ≤ q
  query : (coins : Fin (2 ^ randomBits)) → Fin (queryCount coins) → QueryAddress n
  decision : (coins : Fin (2 ^ randomBits)) → BitInput (queryCount coins) → Bool
</pre>

[Statement.lean, lines 1293–1296](../Statement.lean#L1293-L1296)

<pre title="Statement.lean, lines 1293–1296">
/-- Appendix A: "outputs P (zk1 , zk2 , . . . , zkq )." -/
def NonadaptiveVerifier.accepts {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (coins : Fin (2 ^ V.randomBits)) : Bool :=
  V.decision coins (fun j =&gt; oracleValue input proof (V.query coins j))
</pre>

[Statement.lean, lines 1298–1302](../Statement.lean#L1298-L1302)

<pre title="Statement.lean, lines 1298–1302">
/-- Definition 20: "accepts oracle y ◦ π with probability at most s(|x|)." -/
noncomputable def NonadaptiveVerifier.fraction {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) : ℝ :=
  ((Finset.univ.filter fun coins =&gt; V.accepts input proof coins = true).card : ℝ) /
    (2 ^ V.randomBits : ℝ)
</pre>

[Statement.lean, lines 1304–1307](../Statement.lean#L1304-L1307)

<pre title="Statement.lean, lines 1304–1307">
/-- Definition 20: "there is a proof π". A finite proof has zero values
outside its domain; every queried address is required to lie in its domain. -/
def finiteProofOracle {length : ℕ} (proof : BitInput length) : ℕ → Bool :=
  fun address =&gt; if h : address &lt; length then proof ⟨address, h⟩ else false
</pre>

[Statement.lean, lines 1309–1313](../Statement.lean#L1309-L1313)

<pre title="Statement.lean, lines 1309–1313">
/-- Definition 20: "non-adaptive queries." The bit tag separates input from
proof addresses; both addresses use ordinary self-delimited binary notation. -/
def queryAddressWord {n : ℕ} : QueryAddress n → List Bool
  | .inl i =&gt; false :: RepairOrdinary.frame i.val.bits
  | .inr address =&gt; true :: RepairOrdinary.frame address.bits
</pre>

[Statement.lean, lines 1315–1317](../Statement.lean#L1315-L1317)

<pre title="Statement.lean, lines 1315–1317">
/-- Definition 20: "V (x) tosses r(|x|) random coins". -/
abbrev CoinRequest {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :=
  Σ C : SourceCircuit, Fin (2 ^ (V C).randomBits)
</pre>

[Statement.lean, lines 1319–1323](../Statement.lean#L1319-L1323)

<pre title="Statement.lean, lines 1319–1323">
/-- Definition 20: "makes at most q(|x|) non-adaptive queries". The source
query procedure reports its actual query count before any oracle answers. -/
def coinRequestWord {q : ℕ} {V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q}
    (p : CoinRequest V) : List Bool :=
  sourceCircuitWord p.1 ++ RepairOrdinary.frame p.2.val.bits
</pre>

[Statement.lean, lines 1325–1327](../Statement.lean#L1325-L1327)

<pre title="Statement.lean, lines 1325–1327">
/-- Appendix A: "positions k1 = k1 (C, R), k2 = k2 (C, R), ...". -/
abbrev QueryRequest {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :=
  Σ C : SourceCircuit, Σ coins : Fin (2 ^ (V C).randomBits), Fin ((V C).queryCount coins)
</pre>

[Statement.lean, lines 1329–1334](../Statement.lean#L1329-L1334)

<pre title="Statement.lean, lines 1329–1334">
/-- Appendix A: "positions k1 = k1 (C, R), k2 = k2 (C, R), ...".
The input promise only restricts the supplied coin and query indices. -/
def queryRequestWord {q : ℕ} {V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q}
    (p : QueryRequest V) : List Bool :=
  sourceCircuitWord p.1 ++ RepairOrdinary.frame p.2.1.val.bits ++
    RepairOrdinary.frame p.2.2.val.bits
</pre>

[Statement.lean, lines 1336–1338](../Statement.lean#L1336-L1338)

<pre title="Statement.lean, lines 1336–1338">
/-- Appendix A: "computes a predicate P = P (C, R) on these bits". -/
abbrev DecisionRequest {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :=
  Σ C : SourceCircuit, Σ coins : Fin (2 ^ (V C).randomBits), BitInput ((V C).queryCount coins)
</pre>

[Statement.lean, lines 1340–1343](../Statement.lean#L1340-L1343)

<pre title="Statement.lean, lines 1340–1343">
/-- Appendix A: "computes a predicate P = P (C, R) on these bits". -/
def decisionRequestWord {q : ℕ} {V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q}
    (p : DecisionRequest V) : List Bool :=
  sourceCircuitWord p.1 ++ RepairOrdinary.frame p.2.1.val.bits ++ List.ofFn p.2.2
</pre>

[Statement.lean, lines 1345–1347](../Statement.lean#L1345-L1347)

<pre title="Statement.lean, lines 1345–1347">
/-- Lemma 22: "given the pair (C, w) ∈ Circuit-Eval". -/
abbrev AcceptedSourceInput := Σ C : SourceCircuit,
  {input : BitInput C.arity // C.circuit.eval input = true}
</pre>

[Statement.lean, lines 1349–1352](../Statement.lean#L1349-L1352)

<pre title="Statement.lean, lines 1349–1352">
/-- Lemma 22: "given the pair (C, w) ∈ Circuit-Eval". This is a promise,
not an instruction for the honest algorithm to test circuit acceptance. -/
def acceptedSourceWord (p : AcceptedSourceInput) : List Bool :=
  sourceCircuitWord p.1 ++ List.ofFn p.2.val
</pre>

[Statement.lean, lines 1354–1357](../Statement.lean#L1354-L1357)

<pre title="Statement.lean, lines 1354–1357">
/-- Source p.19:11: "hamming distance more than δn from all y that satisfy E". -/
def StrictlyFar (eta : ℚ) (C : SourceCircuit) (input : BitInput C.arity) : Prop :=
  ∀ accepted : BitInput C.arity, C.circuit.eval accepted = true →
    (eta : ℝ) &lt; PublishedSources.PCPP.relativeHamming input accepted
</pre>

[Statement.lean, lines 1359–1385](../Statement.lean#L1359-L1385)

<pre title="Statement.lean, lines 1359–1385">
/-- Lemma 22: "For any constants 0 &lt; δ, s &lt; 1, there is a PCP of
proximity system for Circuit-Eval with proximity δ, soundness s, number of
random bits r = O(log n) and query complexity q = O(1). Moreover, given the
pair (C, w) ∈ Circuit-Eval, a proof π making V (C) always accepts can be
constructed in poly(|C| + |w|) time."

Only the instance s=1/2 used in Appendix A is imported. Uniform query and
decision procedures are explicit. The finite proof length is unconstrained;
its polynomial trimmed replacement is proved, not assumed. `clog (L+2)` is
the total small-length convention for O(log L), with the constant existential. -/
def Lemma22Half : Prop :=
  ∀ eta : ℚ, 0 &lt; eta → eta &lt; 1 →
    ∃ q : ℕ, ∃ V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q,
    ∃ proofLength : SourceCircuit → ℕ,
      (∀ C coins j address, (V C).query coins j = .inr address → address &lt; proofLength C) ∧
      (∃ a : ℕ, ∀ C, (V C).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord C).length + 2)) ∧
      SourcePolyTime sourceCircuitWord (fun C =&gt; (V C).randomBits.bits) ∧
      SourcePolyTime (coinRequestWord (V := V)) (fun p =&gt; ((V p.1).queryCount p.2).bits) ∧
      SourcePolyTime (queryRequestWord (V := V))
        (fun p =&gt; queryAddressWord ((V p.1).query p.2.1 p.2.2)) ∧
      SourcePolyTime (decisionRequestWord (V := V))
        (fun p =&gt; [(V p.1).decision p.2.1 p.2.2]) ∧
      (∀ C input, StrictlyFar eta C input → ∀ proof : BitInput (proofLength C),
        (V C).fraction input (finiteProofOracle proof) ≤ (1 / 2 : ℝ)) ∧
      ∃ honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1),
        (∀ p coins, (V p.1).accepts p.2.val (finiteProofOracle (honest p)) coins = true) ∧
        SourcePolyTime acceptedSourceWord (fun p =&gt; List.ofFn (honest p))
</pre>
<!-- /statement -->
