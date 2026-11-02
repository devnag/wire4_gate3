# Published statements and their proved consequences

The release theorem has the type `NearQuarticWires.Release.ReleaseStatement`, which is
`PublishedInputs → JointStatement4`. **PublishedInputs has six fields.** The eight pages below
follow the eight intermediate interfaces used by the lower-bound proof; each page identifies its retained source
premises and actual Lean producer. The BCGT input uses the proof-established fixed-tuple soundness bound, not the
constant printed in Theorem 11.1. Four of the interfaces need no published premise. The pages keep the
numbers of the gate companion's mapping, whose page 4 (prime density from the prime number theorem) is omitted:
the proof does not use the prime number theorem.

| Page | Derived interface | Published premises | Closing theorem under `NearCubicGates.Adapters` |
|---|---|---|---|
| [1](1-threshold-normalization.md) | Integer threshold normalization | None | `Normalization.threshold_normalization` |
| [2](2-live-restriction.md) | Central-binomial restriction bound | None | `Restriction.centralBinomialRestriction` |
| [3](3-bernstein.md) | Finite Bernstein inequality | None | `Probability.finiteBernstein` |
| [5](5-rectangular-product.md) | Binary multitape rectangular product | Williams Corollary 4.4 = C.2 | `Williams.Final.williams14_of_leaf` |
| [6](6-short-pcp.md) | Short PCP with an ordinary circuit-construction machine | BCGT Theorem 11.1 at (2,4,0,1), with the proof-established soundness constant, and Algorithm 17 | `Assembly.Fixed.field6OrdinaryFixed` |
| [7](7-refuter.md) | Full-range framed refuter | None | `Assembly.field7` |
| [8](8-amplification.md) | Full-range hardness amplification | STV Theorem 29 | `Amplification.field8` |
| [9](9-three-query-pcpp.md) | Three-query proximity and an efficient linear encoder | CW19 Lemma 22 at half soundness and Lemma 26 | `Assembly.field9Encoder` |
| [Main](main-theorem.md) | Near-quartic wires and near-cubic gates (the joint statement) | The six statements above, through all eight derived interfaces | Type `NearQuarticWires.Release.ReleaseStatement` |

The exact six premise names, under `NearCubicGates.Published`, are `CW19Proximity.Lemma22Half`,
`CW19Code.Lemma26`, `BCGT13.BCGT13_Theorem11_1_Fixed`, `Shoup.FindIrrPolyAlgorithm17`, `STV.Theorem29` and
`Williams.RectangularProductLeaf`. In the release their definitions and source
models are in [Statement.lean](../Statement.lean). [NineInputs.lean](../NineInputs.lean) contains the intermediate
statements; it is not an additional trusted boundary. The trusted statement files are Statement.lean and
Proof/Quartic/Statement/Final.lean, Joint.lean and Release.lean.
[StatementSupport.lean](../StatementSupport.lean) is supporting proof code, checked with the proof; these
statement files do not import it.

## Results of independent interest

Two results that do not mention circuits have their own pages, in the same format as the main page: the paper's
statement beside the Lean declarations, verbatim.

| Page | Result | Lean |
|---|---|---|
| [Tomography](tomography.md) | Modular discrete tomography (Theorem 1.3 of the paper) | `NearQuarticWires.Tomography.residueCounts_determine`, `reconstruct` |
| [Masks](masks.md) | Integer threshold masks (the paper's mask lemma) | `NearQuarticWires.Mask.cutoff_eq_newton_sum_of_le` |

## Reading the correspondence

The mathematical meanings and source conventions must be reviewed against the publications. A source's informal
phrase “polynomial time” does not specify a tape layout. The retained statements therefore state the chosen source
encodings and conventional machine semantics explicitly. Their budgets charge the entire encoded input. An
ordinary `WordFunction` uses one fixed program, input framing of length 2|w|+1, a fresh output tape and exact output
words, including trailing zero bits. These are representation conventions, not words quoted from the publications.

Conversions to the proof's target formats are proved in `SourceAdapters/`. This includes finite-alphabet
simulation for Williams, bounded simulation and ordinary-to-TM2 compilation, verifier/circuit serialization,
proof-address trimming and honest-proof restriction. Each theorem supplies its particular time bound; we do not
assume a universal constant-overhead equivalence of all machine models.

Some retained statements specialize or weaken the printed result. The BCGT input fixes (2,4,0,1), whose
exponents are positive, and uses the soundness term established by its Section 11 argument: 16κ^{log₂c}, rather
than the printed (2^{η+1}+κ^{log c})/(1−2^{−η}). The generic printed statement remains a separate record, not a
release premise. The STV input retains existence of a successful list of machines rather than its randomized
reconstruction algorithm; its degree-zero case is the elementary constant-polynomial extension described on
[page 8](8-amplification.md). The relevant pages spell out these choices. CTW26, Vershynin, Murray–Williams and
CLW20 remain useful mathematical credits for derived statements; they are not extra fields of `PublishedInputs`.

## Paper and verification scope

References use labels in the current [paper](../paper/near-cubic-gates-v3.tex), version 3 (October 28, 2026), SHA-256
`acabd90c76bdabdcccafe7e598b92f46089115a28603a97799c13c372a94d7aa`. The earlier version-2 excerpts and their line
numbers do not describe this file. The input pages link to current producer modules and name declarations
directly; they do not claim to print the complete constant closure of the final statement. The main page quotes
the joint paper, [paper.tex](../paper/paper.tex), SHA-256
`32c365c3c97134031d57cc7fe42432513408376fadb04ada31f3a9205b38070e`, and uses its labels. It prints every
declaration of the statement files in the closure of `JointStatement4`, verbatim; `check.py` re-renders these
excerpts from the statement files and the joint paper and compares them byte for byte.

Run `python3 SourceMapping/check.py` from the release root to check the documentation manifest. File identity,
the six-premise/eight-interface inventory, local links, paper labels and source quotation checks are distinct
from mathematical review. The checker reports missing source files and formula transcriptions separately; a
local identity PASS does not mean every quotation was checked against a source PDF. The Lean build, `Check.lean`
and comparator have the separate roles described in the [repository README](../README.md).

Source provenance is explicit on each page. BCGT Algorithm 17 and Shoup's Corollary 3.2 in the technical-report
version (UW–Madison Computer Sciences Technical Report 763, April 1988, §3) were checked directly; the
author-hosted journal preprint also corroborates the algorithm in Theorem 3.2. [Page 6](6-short-pcp.md) gives the
exact version, source hash and statement.
