The paper is Dev Nag, *Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits*, dated
November 2, 2026. Its LaTeX source is `paper.tex` (SHA-256 `32c365c3c97134031d57cc7fe42432513408376fadb04ada31f3a9205b38070e`), with these
included files:

| File | Content | SHA-256 |
|---|---|---|
| `published-inputs.tex` | The list of the six published inputs | `2717e8d40bedc319bd28c1d34a697b1dfb3bdf2a9dc987b332b63fce11d06dc1` |
| `proof-dag.tex` | The proof diagram | `217240bd5db57969b839a2a18f0f67153012f48f2d149f7523cf40ac5cb0263f` |
| `fig-cell.tex` | The figure of a product-star cell | `f94e7b33f7cb14325325bb3438e2b1a6f8b0711838b1666cc094f331fe1e681b` |
| `app-attribution.tex` | Attribution appendix | `016b2cf1dcb7e4ff7936d123244a9e11a25b4be9414f7bb5438369d5feb11014` |
| `app-lean-map.tex` | The formal counterparts of the proof diagram (included by `app-attribution.tex`) | `0ecb5a08d7b9cc3c1f2606cc49681e536acf8649e21064de526854ff62e909b1` |
| `app-statements.tex` | Supporting statements | `c3c922fce3f89d73ede02fa162315024ac9adda7d1702cee2fb2234c2c389f4b` |
| `app-earlier.tex` | Proofs of the earlier components, with their origins credited | `eca21161503837a002b3cf9ac8fac4ad98da3dbd0429b5359d8d040a6600ee88` |
| `joint-statement-verbatim.txt` | The joint theorem's statement as plain text | `f8c8c719c3607bbbfd6e33fe2ee04e263816483d65669412ee03fe9c90854c9f` |

`paper.pdf` is the supplied compiled paper (SHA-256 `02f54f0282e98b2b1ffb8f1894d4a0cd4b9fe12e5f2550188dba25fd7fda7776`). To rebuild it, run `pdflatex paper.tex` twice in this directory.

`near-cubic-gates-v3.tex` is the LaTeX source of the near-cubic gate companion, Dev Nag, *Almost-Everywhere
Near-Cubic Gate Lower Bounds for SYM∘THR Circuits*, version 3, dated October 28, 2026 (SHA-256
`acabd90c76bdabdcccafe7e598b92f46089115a28603a97799c13c372a94d7aa`). It is kept because the input pages of the source mapping cite
its labels. [Version 1](https://doi.org/10.5281/zenodo.23224160) and
[version 2](https://doi.org/10.5281/zenodo.23405983) of the companion are archival versions; their dates and line
numbers do not identify this source.

The papers are licensed under [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/).
The Lean companion's correspondence with the joint theorem and the six published premises is described in
[SourceMapping](../SourceMapping/README.md).
