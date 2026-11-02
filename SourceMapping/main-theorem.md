# Main theorem: near-quartic wires and near-cubic gates (`thm:main`, `thm:gates`)

<!-- page main=NearQuarticWires.Release.ReleaseStatement -->

[Mapping index](README.md) · the theorem the proof concludes

The release theorem has the type `NearQuarticWires.Release.ReleaseStatement`: the six retained source inputs of
`NearCubicGates.Close.PublishedInputs` imply `NearQuarticWires.Statement.JointStatement4`, the joint statement of
the wire theorem (`thm:main`) and the gate corollary (`thm:gates`). The input pages of this mapping (one per derived
interface) document the source results, including the proof-established fixed-tuple BCGT bound on
[page 6](6-short-pcp.md); this page documents the conclusion.

The first row is the paper's two results beside the Lean propositions that state them. The other rows show every
definition those propositions use, beside the paper's own definitions. The last row is the release statement: the
published inputs imply the joint statement.

<!-- closure -->
The Lean column prints every declaration that `NearQuarticWires.Statement.JointStatement4` uses: all 60 declarations of its closure in the statement files, each exactly as it appears there. The closure stops at Lean's core library and Mathlib, whose definitions are not printed. Its 76 other constants are the constructors, fields and recursors of the printed structures and inductive types, and constants that Lean generates while elaborating the printed declarations.
<!-- /closure -->

**Paper.** The paper is the joint paper, [`paper/paper.tex`](../paper/paper.tex), the sealed version of
November 2, 2026 (SHA-256 `32c365c3c97134031d57cc7fe42432513408376fadb04ada31f3a9205b38070e`); its list of published
inputs is the macro of [`paper/published-inputs.tex`](../paper/published-inputs.tex). The quotations are their LaTeX
source, verbatim, with line numbers of those files. The machine-model row also quotes the near-cubic gate paper,
version 3 ([`paper/near-cubic-gates-v3.tex`](../paper/near-cubic-gates-v3.tex)), whose machine model the joint paper's running-time analysis
uses and whose class `E^NP` the Lean definition `InENP` formalizes.

<!-- files -->
**Files.** The line numbers below are of these files:

- [`paper/paper.tex`](../paper/paper.tex), SHA-256 `32c365c3c97134031d57cc7fe42432513408376fadb04ada31f3a9205b38070e`
- [`Proof/Quartic/Statement/Joint.lean`](../Proof/Quartic/Statement/Joint.lean), SHA-256 `761a4e23b25a9f923ae295e908810518c0ceb77acfb8e4fcf54fdec1949c4efc`
- [`Statement.lean`](../Statement.lean), SHA-256 `6b93f577aab5e326bc174770f9c0bb751e5e78d34820711347888bf0b7bd89e5`
- [`Proof/Quartic/Statement/Final.lean`](../Proof/Quartic/Statement/Final.lean), SHA-256 `8fc2d786784627fbc9325a3f3ccbd82c10982c4e3b11b3cd7cf73d5da70ac810`
- [`paper/near-cubic-gates-v3.tex`](../paper/near-cubic-gates-v3.tex), SHA-256 `acabd90c76bdabdcccafe7e598b92f46089115a28603a97799c13c372a94d7aa`
- [`paper/published-inputs.tex`](../paper/published-inputs.tex), SHA-256 `2717e8d40bedc319bd28c1d34a697b1dfb3bdf2a9dc987b332b63fce11d06dc1`
- [`Proof/Quartic/Statement/Release.lean`](../Proof/Quartic/Statement/Release.lean), SHA-256 `6d5ed3ce062f5443aac46fa97ca1c86fa755e1d49304eaacf9a3f99cb875594e`
<!-- /files -->

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>

<!-- paper file=paper/paper.tex label=thm:main -->
<b>paper/paper.tex, lines 240–251</b> ([paper/paper.tex](../paper/paper.tex#L240-L251))

<pre>
\begin{theorem}[Almost-everywhere near-quartic wire lower bound]
\label{thm:main}
Let \(0&lt;\gamma&lt;1\) be a fixed absolute constant: the rational rejection gap of the three-query PCP of proximity of Chen and Williams~\cite[Lemma~24]{CW19} (\cref{imp:transfer-pcpp}). For every fixed \(0&lt;d&lt;\gamma/5\) there are
a positive integer \(K_d\), a language \(F_d\in\ENP\), and an
integer \(n_0\ge4\) such that, for every \(n\ge n_0\) and every
\(\SYM\circ\THR\) circuit \(C\) on \(n\) inputs,
\[
 \boxed{\quad
 W(C)\le\Bigl\lfloor\frac{n^4}{K_d\,\lambda_n^{17/4}\mu_n^{15/2}}\Bigr\rfloor
 \quad\Longrightarrow\quad \agr(C,F_d)&lt;1-d .\quad}
\]
\end{theorem}
</pre>
<!-- /paper -->

<!-- paper file=paper/paper.tex label=thm:gates -->
<b>paper/paper.tex, lines 253–266</b> ([paper/paper.tex](../paper/paper.tex#L253-L266))

<pre>
\begin{corollary}[Almost-everywhere near-cubic gate lower bound]
\label{thm:gates}\label{cor:gates}
With \(\gamma\), \(d\), \(K_d\), \(F_d\), and \(n_0\) as in
\cref{thm:main}, for every \(n\ge n_0\), every \(\SYM\circ\THR\)
circuit \(C\) on \(n\) inputs satisfies
\[
 \boxed{\quad
 G\le\Bigl\lfloor\frac{n^3}{2K_d\,\lambda_n^{17/4}\mu_n^{15/2}}\Bigr\rfloor
 \quad\Longrightarrow\quad \agr(C,F_d)&lt;1-d .\quad}
\]
More generally, the same conclusion holds for
\(C(x)=g(\sum_i c_iT_i(x))\), with integers \(c_i\ne0\), when
\(\sum_i|c_i|\) is at most the same cap.
\end{corollary}
</pre>
<!-- /paper -->

</td><td>

<!-- lean NearQuarticWires.Statement.JointStatement4 -->
[Proof/Quartic/Statement/Joint.lean, lines 61–63](../Proof/Quartic/Statement/Joint.lean#L61-L63)

<pre title="Proof/Quartic/Statement/Joint.lean, lines 61–63">
/-- **The joint theorem** (`thm:main` and `thm:gates`), with `γ` quantified as in `FinalStatement4`. -/
def JointStatement4 : Prop :=
  ∃ gamma : ℚ, 0 &lt; gamma ∧ gamma &lt; 1 ∧ JointAt4 gamma
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Statement.JointAt4 -->
[Proof/Quartic/Statement/Joint.lean, lines 53–59](../Proof/Quartic/Statement/Joint.lean#L53-L59)

<pre title="Proof/Quartic/Statement/Joint.lean, lines 53–59">
/-- `thm:main` and `thm:gates` together for a fixed rational `γ`: for every fixed `0 &lt; d &lt; γ/5` there are a
positive integer `K_d`, a language `F_d ∈ E^NP` and `n₀ ≥ 4` such that all three conclusions (wires, gates, weighted
gates) hold at every `n ≥ n₀`. -/
def JointAt4 (gamma : ℚ) : Prop :=
  ∀ d : ℝ, 0 &lt; d → d &lt; (gamma : ℝ) / 5 →
    ∃ K : ℕ, 0 &lt; K ∧ ∃ F : Language, InENP F ∧
      ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → WiresAt K F d n ∧ SymGatesAt K F d n ∧ GatesAt K F d n
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Statement.WiresAt -->
[Proof/Quartic/Statement/Joint.lean, lines 49–51](../Proof/Quartic/Statement/Joint.lean#L49-L51)

<pre title="Proof/Quartic/Statement/Joint.lean, lines 49–51">
/-- The conclusion of `thm:main` for constants `K`, `F`, `d` at length `n`. -/
def WiresAt (K : ℕ) (F : Language) (d : ℝ) (n : ℕ) : Prop :=
  ∀ C : SymmetricThresholdCircuit n, wires C ≤ wireCap K n → agr C F &lt; 1 - d
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Statement.SymGatesAt -->
[Proof/Quartic/Statement/Joint.lean, lines 37–41](../Proof/Quartic/Statement/Joint.lean#L37-L41)

<pre title="Proof/Quartic/Statement/Joint.lean, lines 37–41">
/-- The gate count conclusion of `thm:gates` for constants `K`, `F`, `d` at length `n`: every `SYM∘THR` circuit on
`n` inputs with at most `gateCap K n` gates (occurrences, `G = C.bottomCount`) agrees with `F` on less than a `1 − d`
fraction of inputs. -/
def SymGatesAt (K : ℕ) (F : Language) (d : ℝ) (n : ℕ) : Prop :=
  ∀ C : SymmetricThresholdCircuit n, C.bottomCount ≤ gateCap K n → agr C F &lt; 1 - d
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Statement.GatesAt -->
[Proof/Quartic/Statement/Joint.lean, lines 43–47](../Proof/Quartic/Statement/Joint.lean#L43-L47)

<pre title="Proof/Quartic/Statement/Joint.lean, lines 43–47">
/-- The general form of `thm:gates` for constants `K`, `F`, `d` at length `n`: every circuit `g(Σ_i c_i T_i)` with
integer top weights (the class `𝒲` of the near-cubic gate theorem) on `n` inputs with charged top weight
`Σ_i |c_i|` at most `gateCap K n` agrees with `F` on less than a `1 − d` fraction of inputs. -/
def GatesAt (K : ℕ) (F : Language) (d : ℝ) (n : ℕ) : Prop :=
  ∀ C : WeightedSymmetricCircuit n, C.topWeight ≤ gateCap K n → agreement C F &lt; 1 - d
</pre>
<!-- /lean -->

</td></tr>
<tr><td>

<!-- paper file=paper/paper.tex from="A \(\SYM\circ\THR\) circuit first computes threshold gates" to="\(\sum_iT_i(x)\) of gates that output one." -->
<b>paper/paper.tex, lines 168–174</b> ([paper/paper.tex](../paper/paper.tex#L168-L174))

<pre>
A \(\SYM\circ\THR\) circuit first computes threshold gates
\[
 T_i(x)=\ind\Bigl[\sum_{l=1}^n w_{i,l}x_l\ge\theta_i\Bigr],
 \qquad w_{i,l},\theta_i\in\R,
\]
and applies an arbitrary Boolean lookup to the number
\(\sum_iT_i(x)\) of gates that output one. The lookup may test a
</pre>
<!-- /paper -->

<!-- paper file=paper/paper.tex label=def:class -->
<b>paper/paper.tex, lines 202–226</b> ([paper/paper.tex](../paper/paper.tex#L202-L226))

<pre>
\begin{definition}[Circuits and wires]\label{def:class}
A \(\SYM\circ\THR\) circuit on \(n\) inputs has the form
\[
 C(x)=g\Bigl(\sum_{i=1}^{G}T_i(x)\Bigr),
\]
where \(T_1,\dots,T_G\) are threshold gates with real parameters,
called the \emph{bottom gates} of the circuit (repetitions are allowed
and counted), and \(g:\{0,\dots,G\}\to\{0,1\}\) is arbitrary, called
the \emph{lookup}. Let \(f_i\) be the number of inputs \(l\) with
\(w_{i,l}\ne0\), the \emph{fan-in} of \(T_i\). The \emph{wire count}
is
\[
 W(C)=G+\sum_{i=1}^Gf_i,
\]
the top fan-in plus the total bottom fan-in.

\emph{Integer-weighted extension.} \Cref{thm:gates} also covers circuits
\[
 C(x)=g\Bigl(\sum_{i=1}^{G}c_iT_i(x)\Bigr),\qquad
 c_i\in\Z\setminus\{0\},\quad g:\Z\to\{0,1\},
\]
charged by their \emph{total top weight} \(\topwt(C)=\sum_i|c_i|\),
which equals \(G\) when all \(c_i=1\). Bottom fan-in and real bottom
weights are unrestricted in both models.
\end{definition}
</pre>
<!-- /paper -->

</td><td>

<!-- lean NearCubicWires.BitInput -->
[Statement.lean, line 86](../Statement.lean#L86)

<pre title="Statement.lean, line 86">
abbrev BitInput (n : ℕ) := Fin n → Bool
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.bitAsReal -->
[Statement.lean, line 92](../Statement.lean#L92)

<pre title="Statement.lean, line 92">
def bitAsReal (bit : Bool) : ℝ := if bit then 1 else 0
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RealThresholdGate -->
[Statement.lean, lines 94–99](../Statement.lean#L94-L99)

<pre title="Statement.lean, lines 94–99">
/-- A semantic threshold gate together with its exact retained support. -/
structure RealThresholdGate (n : ℕ) where
  weight : Fin n → ℝ
  threshold : ℝ
  support : Finset (Fin n)
  mem_support_iff : ∀ i, i ∈ support ↔ weight i ≠ 0
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RealThresholdGate.eval -->
[Statement.lean, lines 101–103](../Statement.lean#L101-L103)

<pre title="Statement.lean, lines 101–103">
noncomputable def RealThresholdGate.eval {n : ℕ} (gate : RealThresholdGate n)
    (input : BitInput n) : Bool :=
  decide (gate.threshold ≤ ∑ i, gate.weight i * bitAsReal (input i))
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.SymmetricThresholdCircuit -->
[Proof/Quartic/Statement/Final.lean, lines 33–38](../Proof/Quartic/Statement/Final.lean#L33-L38)

<pre title="Proof/Quartic/Statement/Final.lean, lines 33–38">
/-- A `SYM∘THR` circuit (`def:class`): `bottomCount = G` occurrences of real threshold gates (repetitions are
separate indices of `bottom`) and a lookup `top` read at the number of occurrences that output one. -/
structure SymmetricThresholdCircuit (n : ℕ) where
  bottomCount : ℕ
  bottom : Fin bottomCount → RealThresholdGate n
  top : ℕ → Bool
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.SymmetricThresholdCircuit.eval -->
[Proof/Quartic/Statement/Final.lean, lines 40–43](../Proof/Quartic/Statement/Final.lean#L40-L43)

<pre title="Proof/Quartic/Statement/Final.lean, lines 40–43">
/-- The value `C(x) = g(Σ_i T_i(x))` (`def:class`): the lookup at the number of occurrences that output one. -/
noncomputable def SymmetricThresholdCircuit.eval {n : ℕ}
    (circuit : SymmetricThresholdCircuit n) (input : BitInput n) : Bool :=
  circuit.top ((Finset.univ.filter fun i =&gt; (circuit.bottom i).eval input).card)
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Statement.fanIn -->
[Proof/Quartic/Statement/Final.lean, lines 52–55](../Proof/Quartic/Statement/Final.lean#L52-L55)

<pre title="Proof/Quartic/Statement/Final.lean, lines 52–55">
/-- The fan-in `f_i` of an occurrence `T_i` (`def:class`): "Let `f_i` be the number of
inputs `l` with `w_{i,l} ≠ 0`, the *fan-in* of `T_i`." -/
noncomputable def fanIn {n : ℕ} (T : RealThresholdGate n) : ℕ :=
  (Finset.univ.filter fun l : Fin n =&gt; T.weight l ≠ 0).card
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Statement.wires -->
[Proof/Quartic/Statement/Final.lean, lines 57–61](../Proof/Quartic/Statement/Final.lean#L57-L61)

<pre title="Proof/Quartic/Statement/Final.lean, lines 57–61">
/-- The wire count (`def:class`): `W(C) = G + Σ_{i=1}^G f_i`, "the top fan-in plus the
total bottom fan-in". `G = C.bottomCount` is the number of occurrences; repeated occurrences are separate
indices of `C.bottom` and are counted separately. -/
noncomputable def wires {n : ℕ} (C : SymmetricThresholdCircuit n) : ℕ :=
  C.bottomCount + ∑ i : Fin C.bottomCount, fanIn (C.bottom i)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Target.WeightedSymmetricCircuit -->
[Statement.lean, lines 475–482](../Statement.lean#L475-L482)

<pre title="Statement.lean, lines 475–482">
/-- A representation in the paper's class `𝒲` (`def:class`). Bottom weights are arbitrary
real numbers; signed integral top weights are charged by absolute value. -/
structure WeightedSymmetricCircuit (n : ℕ) where
  bottomCount : ℕ
  bottom : Fin bottomCount → RealThresholdGate n
  coefficient : Fin bottomCount → ℤ
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0
  lookup : ℤ → Bool
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Target.WeightedSymmetricCircuit.topWeight -->
[Statement.lean, lines 484–486](../Statement.lean#L484-L486)

<pre title="Statement.lean, lines 484–486">
def WeightedSymmetricCircuit.topWeight {n : ℕ}
    (C : WeightedSymmetricCircuit n) : ℕ :=
  ∑ i, (C.coefficient i).natAbs
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Target.WeightedSymmetricCircuit.score -->
[Statement.lean, lines 488–490](../Statement.lean#L488-L490)

<pre title="Statement.lean, lines 488–490">
noncomputable def WeightedSymmetricCircuit.score {n : ℕ}
    (C : WeightedSymmetricCircuit n) (x : BitInput n) : ℤ :=
  ∑ i, C.coefficient i * (if (C.bottom i).eval x then 1 else 0)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Target.WeightedSymmetricCircuit.eval -->
[Statement.lean, lines 492–494](../Statement.lean#L492-L494)

<pre title="Statement.lean, lines 492–494">
noncomputable def WeightedSymmetricCircuit.eval {n : ℕ}
    (C : WeightedSymmetricCircuit n) (x : BitInput n) : Bool :=
  C.lookup (C.score x)
</pre>
<!-- /lean -->

</td></tr>
<tr><td>

<!-- paper file=paper/paper.tex from="For \(n\ge4\) write" to="\(\agr(C,F)=\Pr_{x\in\{0,1\}^n}[C(x)=F(x)]\)." -->
<b>paper/paper.tex, lines 231–238</b> ([paper/paper.tex](../paper/paper.tex#L231-L238))

<pre>
For \(n\ge4\) write
\[
 \lambda_n=\lceil\lgx n\rceil,\qquad
 \mu_n=\lceil\lgx\lambda_n\rceil,\qquad
 \mathcal A_4(n)=\frac{n^4}{\lambda_n^{17/4}\mu_n^{15/2}},
\]
and for an \(n\)-input circuit \(C\) and a language \(F\) write
\(\agr(C,F)=\Pr_{x\in\{0,1\}^n}[C(x)=F(x)]\).
</pre>
<!-- /paper -->

</td><td>

<!-- lean NearCubicGates.Target.lambda -->
[Statement.lean, line 508](../Statement.lean#L508)

<pre title="Statement.lean, line 508">
def lambda (n : ℕ) : ℕ := Nat.clog 2 n
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Target.mu -->
[Statement.lean, line 510](../Statement.lean#L510)

<pre title="Statement.lean, line 510">
def mu (n : ℕ) : ℕ := Nat.clog 2 (lambda n)
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Statement.wireCap -->
[Proof/Quartic/Statement/Final.lean, lines 69–75](../Proof/Quartic/Statement/Final.lean#L69-L75)

<pre title="Proof/Quartic/Statement/Final.lean, lines 69–75">
/-- The boxed cap of `thm:main`, literally: `⌊n^4 / (K λ_n^{17/4} μ_n^{15/2})⌋`, with
`λ_n = ⌈log₂ n⌉ = lambda n` and `μ_n = ⌈log₂ λ_n⌉ = mu n` (after `def:class`), real powers, and the floor
taken in `ℕ` (the argument is `≥ 0`). For `n ≥ 4`, `K &gt; 0` it equals `⌊𝒜₄(n)/K⌋` and is equivalent to the
integer test `(K·w)^4 λ^17 μ^30 ≤ n^16` (`Proof/Quartic/Statement/Budget.lean`). -/
noncomputable def wireCap (K n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ 4 /
      ((K : ℝ) * (lambda n : ℝ) ^ ((17 : ℝ) / 4) * (mu n : ℝ) ^ ((15 : ℝ) / 2))⌋₊
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Statement.gateCap -->
[Proof/Quartic/Statement/Joint.lean, lines 31–35](../Proof/Quartic/Statement/Joint.lean#L31-L35)

<pre title="Proof/Quartic/Statement/Joint.lean, lines 31–35">
/-- The boxed cap of `thm:gates`, literally: `⌊n^3 / (2 K λ_n^{17/4} μ_n^{15/2})⌋`, with the same `λ_n`, `μ_n` and
real powers as `wireCap`, and the floor taken in `ℕ`. -/
noncomputable def gateCap (K n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ 3 /
      (2 * (K : ℝ) * (lambda n : ℝ) ^ ((17 : ℝ) / 4) * (mu n : ℝ) ^ ((15 : ℝ) / 2))⌋₊
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.BoolFunction -->
[Statement.lean, line 88](../Statement.lean#L88)

<pre title="Statement.lean, line 88">
abbrev BoolFunction (n : ℕ) := BitInput n → Bool
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.Language -->
[Statement.lean, line 90](../Statement.lean#L90)

<pre title="Statement.lean, line 90">
abbrev Language := (n : ℕ) → BoolFunction n
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Statement.agr -->
[Proof/Quartic/Statement/Final.lean, lines 63–67](../Proof/Quartic/Statement/Final.lean#L63-L67)

<pre title="Proof/Quartic/Statement/Final.lean, lines 63–67">
/-- `agr(C, F) = Pr_{x ∈ {0,1}^n}[C(x) = F(x)]` (after `def:class`), uniform over the `2^n` inputs; `F n` is
the language at length `n`. Same formula as `NearCubicGates.Target.agreement`, for SYM∘THR circuits. -/
noncomputable def agr {n : ℕ} (C : SymmetricThresholdCircuit n) (F : Language) : ℝ :=
  ((Finset.univ.filter fun x : BitInput n =&gt; C.eval x = F n x).card : ℝ) /
    (Fintype.card (BitInput n) : ℝ)
</pre>
<!-- /lean -->

<!-- lean NearCubicGates.Target.agreement -->
[Statement.lean, lines 496–499](../Statement.lean#L496-L499)

<pre title="Statement.lean, lines 496–499">
noncomputable def agreement {n : ℕ} (C : WeightedSymmetricCircuit n)
    (F : Language) : ℝ :=
  ((Finset.univ.filter fun x : BitInput n =&gt; C.eval x = F n x).card : ℝ) /
    (Fintype.card (BitInput n) : ℝ)
</pre>
<!-- /lean -->

</td></tr>
<tr><td>

<!-- paper file=paper/paper.tex from="The standard class \(\ENP\), a usual target of the algorithmic" to="not claimed to be in \(\mathrm P\)." max_lines=40 -->
<b>paper/paper.tex, lines 196–198</b> ([paper/paper.tex](../paper/paper.tex#L196-L198))

<pre>
The standard class \(\ENP\), a usual target of the algorithmic
method, consists of languages decided in \(2^{O(n)}\) time with a
satisfiability oracle; the hard language is not claimed to be in \(\mathrm P\).
</pre>
<!-- /paper -->

<!-- paper file=paper/near-cubic-gates-v3.tex from="inputs. The class \(\ENP\) means that one algorithm computes \(F\)" to="it does not place the hard function in polynomial time." -->
<b>paper/near-cubic-gates-v3.tex, lines 153–156</b> ([paper/near-cubic-gates-v3.tex](../paper/near-cubic-gates-v3.tex#L153-L156))

<pre>
inputs. The class \(\ENP\) means that one algorithm computes \(F\)
in time \(2^{O(n)}\) with a SAT oracle. This supplies a uniform hard
language rather than only a counting argument for its existence;
it does not place the hard function in polynomial time.
</pre>
<!-- /paper -->

</td><td>

<!-- lean NearCubicGates.Target.InENP -->
[Statement.lean, lines 501–506](../Statement.lean#L501-L506)

<pre title="Statement.lean, lines 501–506">
/-- Ordinary deterministic exponential time with an NP oracle. This is an
actual finite-control execution certificate, not an uninterpreted predicate. -/
def InENP (F : Language) : Prop :=
  ∃ oracle : ℕ → Bool,
    Nonempty (RepairSource.EncodedNPVerifier oracle) ∧
    Nonempty (RepairSource.OrdinaryENPCertificate oracle F)
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairSource.OrdinaryENPCertificate -->
[Statement.lean, lines 451–457](../Statement.lean#L451-L457)

<pre title="Statement.lean, lines 451–457">
structure OrdinaryENPCertificate (oracle : ℕ → Bool) (language : Language) where
  program : OrdinaryOracleProgram
  exponent : ℕ
  exponentPositive : 1 ≤ exponent
  computes : ∀ n (input : BitInput n),
    OrdinaryOracleRuns oracle program (List.ofFn input) (language n input).toNat.bits
      (2 ^ (exponent * max 1 n))
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairSource.EncodedNPVerifier -->
[Statement.lean, lines 438–449](../Statement.lean#L438-L449)

<pre title="Statement.lean, lines 438–449">
/-- An NP verifier for the query predicate: an ordinary verifier whose time and witness length are
polynomial in the length of the binary query word `code.bits`, not in its numeric value. -/
structure EncodedNPVerifier (oracle : ℕ → Bool) where
  verifier : OrdinaryVerifier
  coefficient : ℕ
  coefficientPositive : 1 ≤ coefficient
  degree : ℕ
  correct : ∀ code : ℕ, oracle code = true ↔
    ∃ witness : List Bool,
      witness.length ≤ coefficient * (natBitLength code + 1) ^ degree ∧
      verifier.acceptsAt (coefficient * (natBitLength code + 1) ^ degree)
        code.bits witness
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairSource.OracleReturn -->
[Statement.lean, lines 386–388](../Statement.lean#L386-L388)

<pre title="Statement.lean, lines 386–388">
structure OracleReturn (stateCount : ℕ) where
  onFalse : Fin stateCount
  onTrue : Fin stateCount
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairSource.OrdinaryOracleProgram -->
[Statement.lean, lines 390–394](../Statement.lean#L390-L394)

<pre title="Statement.lean, lines 390–394">
structure OrdinaryOracleProgram where
  base : OrdinaryProgram
  queryTape : Fin base.tapeCount
  queryFresh : queryTape.val ≠ 0
  query : Fin base.stateCount → Option (OracleReturn base.stateCount)
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairSource.OrdinaryOracleProgram.Config -->
[Statement.lean, lines 396–397](../Statement.lean#L396-L397)

<pre title="Statement.lean, lines 396–397">
abbrev OrdinaryOracleProgram.Config (program : OrdinaryOracleProgram) :=
  Configuration program.base.tapeCount program.base.stateCount
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairSource.OrdinaryOracleStep -->
[Statement.lean, lines 399–416](../Statement.lean#L399-L416)

<pre title="Statement.lean, lines 399–416">
/-- One step of an oracle program, with its cost: an ordinary machine step or an oracle query (see the
constructors). -/
inductive OrdinaryOracleStep (oracle : ℕ → Bool) (program : OrdinaryOracleProgram) :
    ℕ → program.Config → program.Config → Prop where
  | local (before after : program.Config)
      (notHalted : program.base.machine.halted before.control = false)
      (notQuery : program.query before.control = none)
      (transition : step program.base.machine before = some after) :
      OrdinaryOracleStep oracle program 1 before after
  | ask (before : program.Config) (bits padding : List Bool)
      (rule : OracleReturn program.base.stateCount)
      (notHalted : program.base.machine.halted before.control = false)
      (atQuery : program.query before.control = some rule)
      (rewound : before.heads program.queryTape = 0)
      (writtenQuery : before.tapes program.queryTape = frame bits ++ padding) :
      OrdinaryOracleStep oracle program ((frame bits).length + 1) before
        { before with control := if oracle (CanonicalBinary.bitsValue bits)
            then rule.onTrue else rule.onFalse }
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairSource.OrdinaryOracleTrace -->
[Statement.lean, lines 418–425](../Statement.lean#L418-L425)

<pre title="Statement.lean, lines 418–425">
inductive OrdinaryOracleTrace (oracle : ℕ → Bool) (program : OrdinaryOracleProgram) :
    ℕ → program.Config → program.Config → Prop where
  | refl (configuration : program.Config) :
      OrdinaryOracleTrace oracle program 0 configuration configuration
  | cons {cost rest : ℕ} {before middle after : program.Config}
      (step : OrdinaryOracleStep oracle program cost before middle)
      (tail : OrdinaryOracleTrace oracle program rest middle after) :
      OrdinaryOracleTrace oracle program (cost + rest) before after
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairSource.OrdinaryOracleRuns -->
[Statement.lean, lines 427–436](../Statement.lean#L427-L436)

<pre title="Statement.lean, lines 427–436">
/-- Inputs and outputs are framed, with a distinct initially blank output tape.
All data preparation, querying and final head movements inside the program
must be present in the counted trace. -/
def OrdinaryOracleRuns (oracle : ℕ → Bool) (program : OrdinaryOracleProgram)
    (input output : List Bool) (budget : ℕ) : Prop :=
  ∃ cost final, cost ≤ budget ∧
    OrdinaryOracleTrace oracle program cost
      (initialConfiguration program.base.machine (program.base.inputTapes input)) final ∧
    program.base.machine.halted final.control = true ∧
    final.tapes program.base.outputTape = frame output
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairSource.frame -->
[Statement.lean, line 367](../Statement.lean#L367)

<pre title="Statement.lean, line 367">
abbrev frame := RepairOrdinary.frame
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairSource.OrdinaryProgram -->
[Statement.lean, line 369](../Statement.lean#L369)

<pre title="Statement.lean, line 369">
abbrev OrdinaryProgram := RepairOrdinary.Program
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairSource.OrdinaryVerifier -->
[Statement.lean, line 371](../Statement.lean#L371)

<pre title="Statement.lean, line 371">
abbrev OrdinaryVerifier := RepairOrdinary.Verifier
</pre>
<!-- /lean -->

</td></tr>
<tr><td>

<!-- paper file=paper/near-cubic-gates-v3.tex from="\paragraph{Machine model.}" to="are fixed polynomial factors." -->
<b>paper/near-cubic-gates-v3.tex, lines 940–948</b> ([paper/near-cubic-gates-v3.tex](../paper/near-cubic-gates-v3.tex#L940-L948))

<pre>
\paragraph{Machine model.}
Algorithms are deterministic or nondeterministic multitape Turing
machines over a binary alphabet, and time counts machine steps. This is
the model of the imported algorithms (\cref{imp:batch,imp:ae-refuter}).
Arithmetic on polynomial-bit integers uses elementary multiword
algorithms. When an algorithm consults a large table inside a loop, it
first sorts the relevant records by key and then merges, which costs a
logarithmic factor over reading the records once. All such overheads
are fixed polynomial factors.
</pre>
<!-- /paper -->

</td><td>

<!-- lean NearCubicWires.natBitLength -->
[Statement.lean, line 57](../Statement.lean#L57)

<pre title="Statement.lean, line 57">
def natBitLength (value : ℕ) : ℕ := Nat.log 2 value + 1
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.CanonicalBinary.bitsValue -->
[Statement.lean, lines 70–72](../Statement.lean#L70-L72)

<pre title="Statement.lean, lines 70–72">
def bitsValue : List Bool → ℕ
  | [] =&gt; 0
  | bit :: rest =&gt; bit.toNat + 2 * bitsValue rest
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.HeadMove -->
[Statement.lean, lines 167–171](../Statement.lean#L167-L171)

<pre title="Statement.lean, lines 167–171">
inductive HeadMove where
  | left
  | stay
  | right
deriving DecidableEq
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.HeadMove.apply -->
[Statement.lean, lines 173–177](../Statement.lean#L173-L177)

<pre title="Statement.lean, lines 173–177">
def HeadMove.apply (move : HeadMove) (head : ℕ) : ℕ :=
  match move with
  | .left =&gt; head - 1
  | .stay =&gt; head
  | .right =&gt; head + 1
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.readTapeBit -->
[Statement.lean, lines 179–180](../Statement.lean#L179-L180)

<pre title="Statement.lean, lines 179–180">
def readTapeBit (tape : List Bool) (position : ℕ) : Bool :=
  tape.getD position false
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.writeTapeBit -->
[Statement.lean, lines 182–189](../Statement.lean#L182-L189)

<pre title="Statement.lean, lines 182–189">
/-- Write one cell, extending a one-sided tape with blank (`false`) cells when
the head is just beyond its currently materialized support. -/
def writeTapeBit : List Bool → ℕ → Bool → List Bool
  | [], 0, value =&gt; [value]
  | [], position + 1, value =&gt; false :: writeTapeBit [] position value
  | _old :: tail, 0, value =&gt; value :: tail
  | old :: tail, position + 1, value =&gt;
      old :: writeTapeBit tail position value
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.Configuration -->
[Statement.lean, lines 191–194](../Statement.lean#L191-L194)

<pre title="Statement.lean, lines 191–194">
structure Configuration (tapeCount stateCount : ℕ) where
  control : Fin stateCount
  heads : Fin tapeCount → ℕ
  tapes : Fin tapeCount → List Bool
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.Configuration.tapeCells -->
[Statement.lean, lines 196–199](../Statement.lean#L196-L199)

<pre title="Statement.lean, lines 196–199">
def Configuration.tapeCells
    {tapeCount stateCount : ℕ}
    (configuration : Configuration tapeCount stateCount) : ℕ :=
  ∑ tape : Fin tapeCount, (configuration.tapes tape).length
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.Configuration.scanned -->
[Statement.lean, lines 201–206](../Statement.lean#L201-L206)

<pre title="Statement.lean, lines 201–206">
def Configuration.scanned
    {tapeCount stateCount : ℕ}
    (configuration : Configuration tapeCount stateCount) :
    Fin tapeCount → Bool :=
  fun tape =&gt; readTapeBit (configuration.tapes tape)
    (configuration.heads tape)
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.Action -->
[Statement.lean, lines 208–215](../Statement.lean#L208-L215)

<pre title="Statement.lean, lines 208–215">
/-- A finite local action: one replacement bit and one unit head move per
tape, plus the next finite control state. -/
structure Action (tapeCount stateCount : ℕ) where
  nextControl : Fin stateCount
  /-- `none` leaves a tape unchanged; `some bit` writes exactly its scanned
  cell. -/
  write : Fin tapeCount → Option Bool
  move : Fin tapeCount → HeadMove
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.Machine -->
[Statement.lean, lines 217–224](../Statement.lean#L217-L224)

<pre title="Statement.lean, lines 217–224">
/-- The transition function has a finite domain (`Fin stateCount` and one bit
per tape), so it is extensionally a finite transition table. -/
structure Machine (tapeCount stateCount : ℕ) where
  descriptionBits : ℕ
  start : Fin stateCount
  halted : Fin stateCount → Bool
  rule : Fin stateCount → (Fin tapeCount → Bool) →
    Option (Action tapeCount stateCount)
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.applyAction -->
[Statement.lean, lines 226–237](../Statement.lean#L226-L237)

<pre title="Statement.lean, lines 226–237">
def applyAction
    {tapeCount stateCount : ℕ}
    (configuration : Configuration tapeCount stateCount)
    (action : Action tapeCount stateCount) :
    Configuration tapeCount stateCount where
  control := action.nextControl
  heads := fun tape =&gt; (action.move tape).apply (configuration.heads tape)
  tapes := fun tape =&gt;
    match action.write tape with
    | none =&gt; configuration.tapes tape
    | some value =&gt;
        writeTapeBit (configuration.tapes tape) (configuration.heads tape) value
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.step -->
[Statement.lean, lines 239–245](../Statement.lean#L239-L245)

<pre title="Statement.lean, lines 239–245">
def step
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (configuration : Configuration tapeCount stateCount) :
    Option (Configuration tapeCount stateCount) :=
  (machine.rule configuration.control configuration.scanned).map
    (applyAction configuration)
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.initialConfiguration -->
[Statement.lean, lines 247–256](../Statement.lean#L247-L256)

<pre title="Statement.lean, lines 247–256">
/-- Explicit tapes are the standard source input.  Any conversion from a
compact request to these tapes must be a separately executed loader. -/
def initialConfiguration
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (inputTapes : Fin tapeCount → List Bool) :
    Configuration tapeCount stateCount where
  control := machine.start
  heads := fun _tape =&gt; 0
  tapes := inputTapes
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.ExecutionReceipt -->
[Statement.lean, lines 258–261](../Statement.lean#L258-L261)

<pre title="Statement.lean, lines 258–261">
structure ExecutionReceipt (tapeCount stateCount : ℕ) where
  final : Configuration tapeCount stateCount
  steps : ℕ
  peakTapeCells : ℕ
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.runFrom -->
[Statement.lean, lines 263–292](../Statement.lean#L263-L292)

<pre title="Statement.lean, lines 263–292">
def runFrom
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount) :
    ℕ → Configuration tapeCount stateCount →
      Option (ExecutionReceipt tapeCount stateCount)
  | 0, configuration =&gt;
      if machine.halted configuration.control then
        some
          { final := configuration
            steps := 0
            peakTapeCells := configuration.tapeCells }
      else none
  | fuel + 1, configuration =&gt;
      if machine.halted configuration.control then
        some
          { final := configuration
            steps := 0
            peakTapeCells := configuration.tapeCells }
      else
        match step machine configuration with
        | none =&gt; none
        | some next =&gt;
            match runFrom machine fuel next with
            | none =&gt; none
            | some suffix =&gt;
                some
                  { final := suffix.final
                    steps := suffix.steps + 1
                    peakTapeCells := max configuration.tapeCells
                      suffix.peakTapeCells }
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.LocalBitMultitape.run -->
[Statement.lean, lines 294–299](../Statement.lean#L294-L299)

<pre title="Statement.lean, lines 294–299">
def run
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (fuel : ℕ) (inputTapes : Fin tapeCount → List Bool) :
    Option (ExecutionReceipt tapeCount stateCount) :=
  runFrom machine fuel (initialConfiguration machine inputTapes)
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairOrdinary.frame -->
[Statement.lean, lines 314–316](../Statement.lean#L314-L316)

<pre title="Statement.lean, lines 314–316">
def frame : List Bool → List Bool
  | [] =&gt; [false]
  | b :: bs =&gt; true :: b :: frame bs
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairOrdinary.Program -->
[Statement.lean, lines 318–324](../Statement.lean#L318-L324)

<pre title="Statement.lean, lines 318–324">
structure Program where
  tapeCount : ℕ
  stateCount : ℕ
  twoTapes : 2 ≤ tapeCount
  machine : Machine tapeCount stateCount
  outputTape : Fin tapeCount
  outputFresh : outputTape.val ≠ 0
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairOrdinary.Program.inputTapes -->
[Statement.lean, lines 326–328](../Statement.lean#L326-L328)

<pre title="Statement.lean, lines 326–328">
def Program.inputTapes (p : Program) (word : List Bool) :
    Fin p.tapeCount → List Bool :=
  fun i =&gt; if i.val = 0 then frame word else []
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairOrdinary.Verifier -->
[Statement.lean, lines 337–342](../Statement.lean#L337-L342)

<pre title="Statement.lean, lines 337–342">
structure Verifier where
  tapeCount : ℕ
  stateCount : ℕ
  twoTapes : 2 ≤ tapeCount
  machine : Machine tapeCount stateCount
  accepting : Fin stateCount → Bool
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairOrdinary.Verifier.inputTapes -->
[Statement.lean, lines 344–347](../Statement.lean#L344-L347)

<pre title="Statement.lean, lines 344–347">
def Verifier.inputTapes (v : Verifier)
    (input witness : List Bool) : Fin v.tapeCount → List Bool :=
  fun i =&gt; if i.val = 0 then frame input
    else if i.val = 1 then frame witness else []
</pre>
<!-- /lean -->

<!-- lean NearCubicWires.RepairOrdinary.Verifier.acceptsAt -->
[Statement.lean, lines 349–352](../Statement.lean#L349-L352)

<pre title="Statement.lean, lines 349–352">
def Verifier.acceptsAt (v : Verifier) (fuel : ℕ)
    (input witness : List Bool) : Prop :=
  ∃ receipt, run v.machine fuel (v.inputTapes input witness) = some receipt ∧
    v.accepting receipt.final.control = true
</pre>
<!-- /lean -->

</td></tr>
<tr><td>

<!-- paper file=paper/paper.tex from="\paragraph{Published foundations.}" to="restates and proves the PCP, refuter and amplification components" -->
<b>paper/paper.tex, lines 623–628</b> ([paper/paper.tex](../paper/paper.tex#L623-L628))

<pre>
\paragraph{Published foundations.}\label{par:five-inputs}
The formal proof assumes exactly \publishedinputcount\ published results from
 four\ papers, listed with exact locators in \cref{sec:formal}.
The BCGT13 verifier input is Theorem~11.1, at the parameter tuple \((2,4,0,1)\) used in this paper~\cite{BCGT13}.
Everything else the formal proof uses is proved in Lean, including the short PCP of Murray--Williams~\cite{MW20}, the refuter and amplification interfaces of Chen--Lyu--Williams~\cite{CLW20}, integer normalization of threshold gates, concentration, and the prime counts from Chebyshev-type bounds.
\Cref{app:earlier} restates and proves the PCP, refuter and amplification components, with their origins credited; the classical normalization, concentration and prime-count facts are cited to their published sources in \cref{app:statements} and \cref{earlier:g:lem:primes}.
</pre>
<!-- /paper -->

<!-- paper file=paper/published-inputs.tex from="\newcommand{\publishedinputcount}" to="\newcommand{\publishedrecord}" -->
<b>paper/published-inputs.tex, lines 1–13</b> ([paper/published-inputs.tex](../paper/published-inputs.tex#L1-L13))

<pre>
\newcommand{\publishedinputcount}{six}
\newcommand{\publishedinputlist}{%
Williams' rectangular multiplication~\cite[Corollary~4.4]{WilACC14};
Ben-Sasson--Chiesa--Genkin--Tromer's verifier in its positive-exponent
domain~\cite[Theorem~11.1]{BCGT13};
the deterministic irreducible-polynomial algorithm of Shoup, as in
\cite[Algorithm~17]{BCGT13};
Sudan--Trevisan--Vadhan's list-decoding theorem~\cite[Theorem~29]{STV01};
Chen--Williams' proximity theorem at soundness \(1/2\)~\cite[Lemma~22]{CW19};

and their linear-code theorem~\cite[Lemma~26]{CW19}%
}
\newcommand{\publishedrecord}{\texttt{PublishedInputs}}
</pre>
<!-- /paper -->

</td><td>

<!-- lean NearCubicGates.Close.PublishedInputs -->
[Statement.lean, lines 1828–1835](../Statement.lean#L1828-L1835)

<pre title="Statement.lean, lines 1828–1835">
/-- The published results the main theorem assumes: one field per published statement above. -/
structure PublishedInputs : Prop where
  williams_rectangularProductLeaf : NearCubicGates.Published.Williams.RectangularProductLeaf
  bcgt13_theorem11_1 : NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1_Fixed
  shoup_findIrrPolyAlgorithm17 : NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17
  stv_theorem29 : NearCubicGates.Published.STV.Theorem29
  cw19Proximity_lemma22Half : NearCubicGates.Published.CW19Proximity.Lemma22Half
  cw19Code_lemma26 : NearCubicGates.Published.CW19Code.Lemma26
</pre>
<!-- /lean -->

<!-- lean NearQuarticWires.Release.ReleaseStatement -->
[Proof/Quartic/Statement/Release.lean, lines 29–31](../Proof/Quartic/Statement/Release.lean#L29-L31)

<pre title="Proof/Quartic/Statement/Release.lean, lines 29–31">
/-- **The release theorem's type** (`thm:main` and `thm:gates`, joint paper `paper/paper.tex`): the
published results of `NearCubicGates.Close.PublishedInputs` imply `JointStatement4`. -/
def ReleaseStatement : Prop := NearCubicGates.Close.PublishedInputs → NearQuarticWires.Statement.JointStatement4
</pre>
<!-- /lean -->

</td></tr>
</table>

## What to check

1. **The two results and their sharing.** `JointAt4` quantifies, for one rational `γ` with `0 < γ < 1` and every real
   `d` with `0 < d < γ/5`, one positive integer `K`, one language `F` with `InENP F` and one onset `n₀ ≥ 4`, and
   asserts at every `n ≥ n₀` all three conclusions: the wire bound (`WiresAt`), the gate bound for `SYM∘THR`
   (`SymGatesAt`) and the bound for charged top weight in the class `𝒲` (`GatesAt`). `thm:gates` says "with `γ`,
   `d`, `K_d`, `F_d`, and `n_0` as in `thm:main`"; one `K`, `F`, `n₀` serving all three conclusions is that sharing.
2. **The caps.** `wireCap K n` is `⌊n^4/(K λ_n^{17/4} μ_n^{15/2})⌋` and `gateCap K n` is
   `⌊n^3/(2K λ_n^{17/4} μ_n^{15/2})⌋`, with real powers and the floor of a nonnegative real. The hypotheses
   `W(C) ≤ cap`, `G ≤ cap` and `Σ|c_i| ≤ cap` are non-strict; the conclusions `agr < 1 − d` are strict, as printed.
3. **The circuits.** A `SYM∘THR` circuit is `SymmetricThresholdCircuit n`: `bottomCount = G` occurrences of real
   threshold gates (repetitions are separate indices) and a lookup on the number of gates that output one. A gate
   outputs one exactly when `Σ_l w_l x_l ≥ θ`, ties included. `fanIn` counts the nonzero weights, and
   `wires C = G + Σ_i fanIn (T_i)`, the paper's `W(C)`. The class `𝒲` is `WeightedSymmetricCircuit n`: nonzero
   integer coefficients, an arbitrary lookup `ℤ → Bool`, `score = Σ_i c_i T_i(x)` and `topWeight = Σ_i |c_i|`, the
   paper's `wt(C)`. `RealThresholdGate` also carries `support` with `mem_support_iff : i ∈ support ↔ weight i ≠ 0`: the support is
   exactly the set of nonzero weights and adds no freedom.
4. **`λ_n`, `μ_n` and `agr`.** `lambda n = Nat.clog 2 n = ⌈log₂ n⌉` and `mu n = ⌈log₂ λ_n⌉`. `agr` and `agreement`
   divide the number of inputs `x ∈ {0,1}^n` on which the circuit agrees with `F n` by `2^n`.
5. **`E^NP`.** `InENP F` asks for an explicit deterministic multitape oracle program deciding `F` in `2^{O(n)}`
   counted steps (an `OrdinaryENPCertificate`) whose oracle language has an NP verifier (`EncodedNPVerifier`),
   both in the machine model of the last-but-one row. Time is counted in steps: a local step costs `1` and an oracle
   query on the word `bits` costs `|frame(bits)| + 1`, its framed length plus one (`OrdinaryOracleStep`).
6. **The release statement.** `ReleaseStatement` is `PublishedInputs → JointStatement4`; the fields are exactly
   the six retained source inputs. The BCGT field uses the repaired fixed-tuple soundness bound described on
   [page 6](6-short-pcp.md), not the full printed sum-form record.
7. **The published statements.** A transcription error in the published statements of `Statement.lean` (sections
   10–15; their definitions are printed on input pages [5](5-rectangular-product.md), [6](6-short-pcp.md),
   [8](8-amplification.md) and [9](9-three-query-pcpp.md)) can make the theorem vacuous: from a false hypothesis the
   release theorem follows trivially. Read these definitions against the sources.

## Documented deviations

- **Floors in ℕ.** The caps take `Nat.floor` (`⌊·⌋₊`) of a nonnegative real; on nonnegative reals it equals the
  paper's floor.
- **Real powers.** `λ_n^{17/4}` and `μ_n^{15/2}` are `Real.rpow` of the casts of `λ_n` and `μ_n`. For `n ≥ 4`,
  `λ_n ≥ 2` and `μ_n ≥ 1`, so the denominators are positive and the powers are the paper's.
- **`n₀ ≥ 4`.** The onset is required to be at least 4, where `λ_n` and `μ_n` are defined in the paper ("For
  `n ≥ 4` write"); `thm:main` states an integer `n_0 ≥ 4`.
- **The constant `γ`.** The formal output asserts existence of a rational `γ` with `0 < γ < 1`, before
  quantifying over `d`. It does not assert the conclusion for every externally specified rejection gap or give
  a numerical value of `γ`. The paper fixes one gap supplied by its three-query proof system; the range of `d`
  uses that same chosen gap.
- **The lookup of a `SYM∘THR` circuit.** The paper's lookup is `g : {0,…,G} → {0,1}`; Lean's `top : ℕ → Bool` is
  read only on `{0,…,G}`, since at most `G` gates output one, so its other values are irrelevant.
- **The oracle of `E^NP`.** The paper's oracle is satisfiability; `InENP` allows the oracle language of any NP
  verifier. Since SAT is NP-complete these give the same class.

## Class

The circuit classes are the paper's two models of `def:class`: `SYM∘THR` (`SymmetricThresholdCircuit`, charged by
`W(C)` in the wire theorem and by `G` in the gate theorem) and the class `𝒲` (`WeightedSymmetricCircuit`, charged by
`wt(C)`). Bottom weights and thresholds are arbitrary reals and bottom fan-in is unrestricted in both. The complexity
class is `E^NP`, formalized as an explicit oracle-machine certificate (`InENP`). The statement of the release theorem
uses only the declarations printed on this page and the six retained source inputs; it is the proposition that
`Check.lean` and the comparator check.
