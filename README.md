# wire4_gate3: near-cubic gate and near-quartic wire lower bounds for SYM∘THR circuits in Lean

This repository formalizes the joint theorem of Dev Nag's *Near-Cubic Gate and Near-Quartic Wire Lower Bounds for
SYM∘THR Circuits*, [November 2, 2026](paper/paper.tex) ([PDF](paper/paper.pdf)). The theorem is
proved from **six source inputs** from the cited papers. The BCGT verifier input is used at the fixed tuple (2,4,0,1),
with the soundness constant that its proof establishes, a weakening of the printed bound described below.
The prime number theorem is not an input. The eight intermediate statements used by the lower-bound proof are
derived in Lean; they are not additional assumptions. DOI: https://doi.org/10.5281/zenodo.23847026 

## Reading guide

1. **The statement.** [Statement.lean](Statement.lean) (the models and the six retained source statements) and
   [Proof/Quartic/Statement/](Proof/Quartic/Statement/) (`Final.lean`, `Joint.lean`, `Release.lean`: the circuit
   class, the wire and gate measures, the joint theorem and the release statement). These are the trusted files.
2. **The mapping.** [SourceMapping/main-theorem.md](SourceMapping/main-theorem.md) prints the paper's theorem
   beside every Lean declaration the release statement uses; the input pages do the same for the published
   statements.
3. **The check.** `make` builds the proof and runs [Check.lean](Check.lean), which prints the statement, the
   published inputs and the axioms, and ends with `PASS`.
4. **The comparator.** `make comparator` in a fresh clone compares [Solution.lean](Solution.lean) with
   [Challenge.lean](Challenge.lean) in a sandbox and replays the proof through Lean's kernel.

## The theorem

A SYM∘THR circuit on n inputs computes C(x) = g(Σ_{i=1}^G T_i(x)), where T_1, …, T_G are threshold gates
T_i(x) = [Σ_l w_{i,l} x_l ≥ θ_i] with real weights and thresholds (repetitions are allowed and counted), and the
lookup g : {0,…,G} → {0,1} is arbitrary. The fan-in f_i of T_i is the number of inputs l with w_{i,l} ≠ 0, and the
wire count is W(C) = G + Σ_i f_i, the top fan-in plus the total bottom fan-in. The class 𝒲 allows nonzero integer
top weights: C(x) = g(Σ_i c_i T_i(x)) with c_i ∈ ℤ ∖ {0} and g : ℤ → {0,1}; its charged top weight is
wt(C) = Σ_i |c_i|. For n ≥ 4 let λ_n = ⌈log₂ n⌉ and μ_n = ⌈log₂ λ_n⌉, and let agr(C, F) be the fraction of inputs
x ∈ {0,1}^n with C(x) = F(x).

**Theorem 1.1** (`thm:main`, wires). There is a rational rejection gap γ with 0 < γ < 1 such that, for every
fixed 0 < d < γ/5, there are a positive integer K_d, a language F_d ∈ E^NP and an integer n₀ ≥ 4
such that, for every n ≥ n₀ and every SYM∘THR circuit C on n inputs,

> W(C) ≤ ⌊n⁴/(K_d λ_n^{17/4} μ_n^{15/2})⌋ implies agr(C, F_d) < 1 − d.

**Corollary 1.2** (`thm:gates`, gates). With the same γ, d, K_d, F_d and n₀, for every n ≥ n₀ every SYM∘THR circuit
C on n inputs satisfies

> G ≤ ⌊n³/(2K_d λ_n^{17/4} μ_n^{15/2})⌋ implies agr(C, F_d) < 1 − d,

and the same conclusion holds for every C ∈ 𝒲 whose charged top weight Σ_i |c_i| is at most the same cap.

So one language in E^NP requires n⁴/polylog n wires and n³/polylog n gates at every large input length, even with a
constant fraction of errors. The constant γ is existential and is not optimized.

## The release statement and its published inputs

The release theorem has the type `NearQuarticWires.Release.ReleaseStatement`
([Proof/Quartic/Statement/Release.lean](Proof/Quartic/Statement/Release.lean)):

```lean
def ReleaseStatement : Prop := NearCubicGates.Close.PublishedInputs → NearQuarticWires.Statement.JointStatement4
```

`JointStatement4` ([Proof/Quartic/Statement/Joint.lean](Proof/Quartic/Statement/Joint.lean)) asserts, for one
rational γ with 0 < γ < 1 and every real 0 < d < γ/5, one K, one F with `InENP F` and one n₀ ≥ 4 serving three
conclusions at every n ≥ n₀: the wire bound (`WiresAt`), the gate bound for SYM∘THR (`SymGatesAt`) and the bound
for charged top weight in 𝒲 (`GatesAt`). Its definitions are in [Statement.lean](Statement.lean),
[Proof/Quartic/Statement/Final.lean](Proof/Quartic/Statement/Final.lean) and `Joint.lean`.
[StatementSupport.lean](StatementSupport.lean) contains supporting definitions and proofs, checked with the proof;
it is not a trusted statement file, and the statement chain does not import it.

`PublishedInputs` retains six source statements in [Statement.lean](Statement.lean). The gate companion's
prime-number-theorem field is omitted. Its BCGT verifier field is restricted to (2,4,0,1) and uses the
proof-established soundness constant below. Names in the second column are under `NearCubicGates.Published`.

| Published result | Lean statement | Used to derive |
|---|---|---|
| Chen–Williams, Lemma 22, at soundness 1/2 | `CW19Proximity.Lemma22Half` | [Three-query proximity](SourceMapping/9-three-query-pcpp.md) |
| Chen–Williams, Lemma 26 | `CW19Code.Lemma26` | [Efficient linear code and encoder](SourceMapping/9-three-query-pcpp.md) |
| Ben-Sasson–Chiesa–Genkin–Tromer, Theorem 11.1 at (2,4,0,1), with the proof-established soundness constant | `BCGT13.BCGT13_Theorem11_1_Fixed` | [Short PCP](SourceMapping/6-short-pcp.md) |
| Deterministic irreducible-polynomial algorithm, BCGT Algorithm 17, citing Shoup | `Shoup.FindIrrPolyAlgorithm17` | [Field construction for the short PCP](SourceMapping/6-short-pcp.md) |
| Sudan–Trevisan–Vadhan, Theorem 29 | `STV.Theorem29` | [Hardness amplification](SourceMapping/8-amplification.md) |
| Williams, Corollary 4.4 = C.2 | `Williams.RectangularProductLeaf` | [Rectangular matrix product](SourceMapping/5-rectangular-product.md) |

For the BCGT input, let κ be the subspace dimension and c the unchanged constant of Theorem 11.3 at (2,4,0,1).
The retained bounds are rejection at least δ/(1+K(κ)) for RS and δ/(2+K(κ)) for VRS, with
K(κ)=16κ^{log₂c} (`repairedSoundTerm`). The verifier, completeness, degree ranges and other quantifiers are
unchanged. The generic `soundTerm` and `BCGT13_Theorem11_1` remain records of the printed sum-form statement;
they are not release inputs. [Page 6](SourceMapping/6-short-pcp.md) gives the source derivation and the four
correction families: Algorithms 21 and 23, the VRS equation, and the soundness/distance estimates, including
checked distance witnesses.

[Threshold normalization](SourceMapping/1-threshold-normalization.md),
[random restrictions](SourceMapping/2-live-restriction.md), [finite Bernstein](SourceMapping/3-bernstein.md) and
the [fixed-machine refuter](SourceMapping/7-refuter.md) are proved without a published premise. The other four
interfaces follow from the six statements above (`NearCubicGates.Adapters.sources_to_nine`). The name
`NineInputs` keeps the gate companion's nine numbered interfaces; omitting its prime-number-theorem input 4
leaves the eight fields of this release ([NineInputs.lean](NineInputs.lean)). Williams' rectangular
product is also the matrix-multiplication step of the counting algorithm. The gate companion's prime-density
interface (its input 4) is omitted: the prime counts the proof needs follow from Chebyshev-type bounds proved in
Lean.

**Start with [the main-theorem mapping](SourceMapping/main-theorem.md).** It quotes `thm:main`, `thm:gates` and the
definitions of the joint paper beside every declaration that `JointStatement4` uses, verbatim, and ends with the
release statement. The [SourceMapping index](SourceMapping/README.md) leads to the eight input pages.

## Verify the release

```bash
git clone https://github.com/devnag/wire4_gate3
cd wire4_gate3
make              # Mathlib cache, build, Check.lean
```

Install [elan](https://github.com/leanprover/elan), then run `make` in the repository. The pinned toolchain is in
[lean-toolchain](lean-toolchain); the build obtains Mathlib's cache, builds the proof and runs
[Check.lean](Check.lean), which prints the release statement, the definitions it uses, the published statements,
the release theorem and its axioms. Its successful result means the compiled theorem has the requested type and uses
only `propext`, `Classical.choice` and `Quot.sound`. A full build needs substantial disk space, memory and time.

For the sandboxed check, use a **separate fresh clone on a clean Linux account or container**, before any ordinary
build. Run `make comparator` there. The command installs the revisions
pinned by [scripts/comparator.sh](scripts/comparator.sh), builds inside the sandbox, compares
[Solution.lean](Solution.lean) with [Challenge.lean](Challenge.lean), checks the permitted axioms and replays the
proof through Lean's kernel. The script refuses a tree containing previously compiled proof files. Comparator's
successful result is `VERDICT: PASS … comparator: Your solution is okay!` with exit status zero. Run `make` on
platforms where this wrapper is unavailable.

Measured on a 90-core machine with 354 GB of RAM, `make comparator` took about 5 hours
(about 2 h 50 min to build, about 2 h 10 min of kernel replay), needed about 80 GB of free
disk space and about one million inodes, and peaked at about 32 GB of memory
(`MEM_GB_MEASURED` in [scripts/comparator.sh](scripts/comparator.sh)). On machines with less memory,
limit Lake's parallel jobs.

Optional checks are `make kernel-replay` (standalone `leanchecker`), `make names`, and
`python3 SourceMapping/check.py` (documentation identity, inventories, labels and links; it re-renders every
verbatim excerpt of the main-theorem mapping from the statement files and the joint paper and compares them byte for
byte). These checks do not establish a mathematical source correspondence or replace the kernel checks.
Without the cited source PDFs, `check.py` reports `source_quote_status: INCOMPLETE`;
`bash scripts/fetch_sources.sh --download` fetches those available at verified direct URLs into
`SourceMapping/pdfs/` (other entries require manual acquisition), and the PDFs are not redistributed.

## Reused and new code

| Namespace | Where | What it is |
|---|---|---|
| `NearCubicGates.*` | [Statement.lean](Statement.lean), [NineInputs.lean](NineInputs.lean), [SourceAdapters/](SourceAdapters/), `Proof/Gates/`, [StatementChecks/](StatementChecks/) | The near-cubic gate companion ([github.com/devnag/near-cubic-gates-lean](https://github.com/devnag/near-cubic-gates-lean)): the six retained source statements and their models, the eight derived interfaces and the adapters from the six to the eight, reused without the companion's prime-number-theorem input |
| `NearCubicWires.*` | `Proof/Wire_3_5/`, `Proof/Foundations/`, `Proof/MachineModel/`, `Proof/Amplification/`, `Proof/PCP/` and the other directories of `Proof/` except `Proof/Gates/` and `Proof/Quartic/`, [Bindings/](Bindings/), [StatementSupport.lean](StatementSupport.lean) | Machine models, word programs and supporting proofs shared with earlier formalizations |
| `NearQuarticWires.*` | `Proof/Quartic/` | New for the joint theorem: the certified counter, its machine and its cost, the wire transfer, the gate corollary, the joint statement and the release statement |

The names `NearCubicGates` and `NearCubicWires` mark code shared with earlier formalizations; they do not change
the theorem stated in `ReleaseStatement`.
The module-name prefixes `Dock`, `Closeout` and `Repair` are retained from earlier proof organization and do not
change the assumptions of `ReleaseStatement`.

## The proof diagram and its formal counterparts

The proof diagram of the joint paper (`fig:proof-dag`) has these formal counterparts (the paper's `tab:lean-nodes`).
Wire names are relative to `NearQuarticWires`; source-adapter and input names are relative to `NearCubicGates`.

| Diagram component | Formal declaration |
|---|---|
| Williams | `Close.PublishedInputs.williams_rectangularProductLeaf` |
| BCGT13 | `Close.PublishedInputs.bcgt13_theorem11_1` |
| Shoup/BCGT | `Close.PublishedInputs.shoup_findIrrPolyAlgorithm17` |
| STV | `Close.PublishedInputs.stv_theorem29` |
| CW proximity | `Close.PublishedInputs.cw19Proximity_lemma22Half` |
| CW code | `Close.PublishedInputs.cw19Code_lemma26` |
| Published-source adapter | `Adapters.sources_to_nine` |
| Refuter | `Adapters.Assembly.field7` |
| Short PCP | `Adapters.Assembly.Fixed.field6OrdinaryFixed` |
| Amplification | `Adapters.Amplification.field8` |
| Three-query PCPP/code | `Adapters.Assembly.field9Encoder` |
| Product-star cells | `Cells.partition_average`; `Cells.mean_population` |
| Bounded-matrix sampler | `Sampler.mean_traceMoment_le`; `Sampler.paper_fourth_root_budget` |
| Cycle-sum identity | `Cycle.cycle_sum_identity`; `Cycle.conditional_cycle_sum_identity` |
| Integer masks | `Mask.maskPoly_eq_mask`; `Mask.indicatorPolynomial_eq_mask` |
| Localization/tomography | `Walks.chain_localization_failure_bound`; `Walks.signed_residue_recovery` |
| Printing | `Cells.compiledTable_value`; `Cells.compiledTable_weightedDominance` |
| Certified counter | `Program.counterExists4` |
| Wire transfer | `Transfer.transfer4_official`; `Program.finalStatement4` |
| Wires and gate outputs | `Statement.WiresAt`; `Statement.SymGatesAt`; `Statement.GatesAt`; `GateCorollary.jointStatement4_of_final` |
| Joint conclusion | `Release.main_from_published`; `Statement.JointStatement4` |

## Reusable results

These results can be cited on their own ([tomography](SourceMapping/tomography.md) and
[masks](SourceMapping/masks.md) print the paper's statements beside the Lean ones); `import Proof.Quartic.Reusable` provides
all of them (the tomography theorems are in `Proof/Quartic/Tomography.lean`). `Check.lean` prints their axioms
and fails unless they are `propext`, `Classical.choice` and `Quot.sound`.

| Lean name | Statement | Paper |
|---|---|---|
| `NearQuarticWires.Tomography.residueCounts_determine`, `.reconstruct` | For a nonempty finite set `P` of primes with window `W = 1 + Σ_{p∈P}(p−1)` and `2 ≤ L ≤ S(⌊(W−1)/(L−1)⌋)`, `S(q) = Σ_{m≤q} m·φ(m)`: a rational function on an `L × L` integer box is determined by its residue counts `Σ{f(x,y) : x ≡ a, y ≡ b (mod p)}`, and a checked rational left inverse recovers it | `thm:modular-tomography` (Theorem 1.3) |
| `NearQuarticWires.Tomography.reconstruct_at_side` | The same at the computable side `⌊⌊√⌊√W⌋⌋³/24⌋`, of order `W^{3/4}`, once `W` is large | after `thm:modular-tomography` |
| `NearQuarticWires.Reusable.scalarCounts_determine`, `.scalar_reconstruct` | For `L ≤ W`, a rational function on `L` consecutive integers is determined by, and recovered from, its residue counts modulo the primes of `P` | one-dimensional tomography |
| `NearQuarticWires.Reusable.threshold_eq_newton_sum` | For `X ≤ X_max`: `[X ≤ τ] = Σ_{a≤X_max} c_a(τ)·C(X,a)` with `c_a(τ) = Σ_{i≤a} (−1)^{a−i} C(a,i) [i ≤ τ]` | `lem:maskpoly` |
| `NearQuarticWires.Reusable.cycle_sum_identity` | At `m = 4`: the column potential `Σ_θ Σ_ν tr(D(E_{θ,ν})^8)` equals `(2·\|Θ\|/4^4)` times a sum over closed eight-step walks alternating rows and columns of `Γ_w · mask_w · Σ_σ κ_σ [Σ_l σ_l R₁ = 0][Σ_l σ_l R₂ = 0]`, `κ_σ = 1 + ∏_l σ_l`: only walks whose two signed score sums vanish contribute | `lem:cycle` |
| `NearQuarticWires.Reusable.mean_population` | Some translation of the product-star partition has mean cell population at most `6·r^{3/2}·W/n^{3/2}` | `lem:meanpop` |
| `NearQuarticWires.Reusable.wireTransfer` | The eight intermediate inputs and a counter satisfying the contract `Transfer.CounterExists4` (the properties (i)–(iv) of `thm:counter` at the cap `W ≤ a·β·𝒜₄(n)`, for every pair of positive exponents) imply the wire lower bound `FinalStatement4`; proved for this cap only | `thm:wire-transfer` |

```lean
import Proof.Quartic.Reusable

example (f g : Fin 2 × Fin 2 → ℚ) (P : Finset ℕ) (hne : P.Nonempty) (hp : ∀ p ∈ P, p.Prime)
    (hsize : 2 ≤ NearCubicGates.TomographyDirections.degreeSum ((NearCubicGates.ScalarWindow.window P - 1) / 1))
    (h : NearQuarticWires.Tomography.residueCounts P 0 0 2 f = NearQuarticWires.Tomography.residueCounts P 0 0 2 g) :
    f = g :=
  NearQuarticWires.Tomography.residueCounts_determine P hne hp 0 0 2 le_rfl hsize h
```

The release also proves the near-cubic gate theorem in its published form, with cap `⌊n³/(K λ_n^{21/4} μ_n^7)⌋`:
`NearQuarticWires.Release.gate_paper_main : PublishedInputs → NearCubicGates.Target.MainStatement`.

## What remains trusted

The trusted statement files are [Statement.lean](Statement.lean) (the six retained source statements and the gate
companion's definitions) and the statement files of [Proof/Quartic/Statement/](Proof/Quartic/Statement/)
(`Final.lean`, `Joint.lean`, `Release.lean`) that define the circuit class, `JointStatement4` and
`ReleaseStatement`; they import Mathlib and each other only. They
contain definitions and the six premises, not the proofs of their consequences. The correctness of the premises
and the faithfulness of their formal meanings to the publications require mathematical review; the
[mapping pages](SourceMapping/README.md) record the conventions and source locators.

Comparator checks the exact challenge statement, the permitted axioms and the kernel proof. It does not check
whether the six retained source statements are true, whether their formal meanings match the source arguments, or whether the conclusion
is the intended paper theorem. Its trusted infrastructure also includes the pinned Lean/Mathlib definitions, build
configuration and sandbox tools. `Challenge.lean` deliberately leaves its proof open for the comparison;
`Solution.lean` supplies the proof.

Machine conventions are explicit. Ordinary programs use finite-control, local multitape transitions and pay for
their input/output representations. The class E^NP is formalized as an explicit oracle-machine certificate
(`InENP`) with an NP verifier for its oracle language. The six source statements document their own model
conventions separately from the downstream encoding conversions proved in the adapters.

## Paper, provenance and license

The joint paper's source is [paper/paper.tex](paper/paper.tex), dated November 2, 2026, SHA-256
`32c365c3c97134031d57cc7fe42432513408376fadb04ada31f3a9205b38070e`, with its included files in [paper/](paper/).
The gate companion's version 3 source, [paper/near-cubic-gates-v3.tex](paper/near-cubic-gates-v3.tex), is kept because the eight input pages cite
its labels.

Generative-AI tools were used to produce the formalization; see the paper's AI methodology statement. Verification
relies on the proof checks and mathematical source review, not on trusting those tools.

Code is [Apache-2.0](LICENSE), except the [papers, licensed CC BY 4.0](paper/README.md). Quoted passages remain their
authors' work. Cite Dev Nag, *Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits*, November 2,
2026.
