# The inverse problem for the number of connected induced subgraphs

**Lucas Alves de Almeida** (independent researcher, lucasderiva8x@gmail.com)

Paper, Lean 4 formalization, programs and data. Version **1.0** (see `VERSION`; checksums in
`MANIFEST.txt`).

## Abstract

For a finite graph $G$, let $c(G)$ be the number of nonempty vertex sets that induce a connected
subgraph. We show that a positive integer $k$ equals $c(G)$ for some finite connected graph $G$ if
and only if $k\notin\{2,4,5,8,9,16\}$. Every attainable value $k\ne25$ is attained on
$\lfloor\log_2k\rfloor+1$ vertices, the least possible number, and $25$ needs six vertices. More
precisely, for every $m\ge6$ each integer from $2^{m-1}$ to $2^m-1$ is the value of $c$ on a
connected graph with exactly $m$ vertices.

The proofs of these results are short and use no computer. Computer calculations serve only as
independent checks, and for two auxiliary results: the values on six to eight vertices, and the
result on all connected subgraphs described below.

The value $16$ falls into a gap above the path: a connected graph on $n\ge4$ vertices other than
the path $P_n$ has at least $n-3$ more connected sets than $P_n$. The values $k\ge17$ are realized
by a recursive construction from cones, disjoint unions and a family of graphs that we call
near-cones, starting from seven small graphs. It produces a graph with $c(G)=k$ in time polynomial
in $\log k$.

The question arose from a problem of Ordoñez in continuum theory, through a reduction by Camargo,
Ordoñez and Ramírez, who found the values up to $255$ by a computer search. The proof is formalized
in Lean 4. We also observe that a theorem of Czabarka, Székely and Wagner on subtrees reduces the
corresponding problem for the number of all connected subgraphs to a finite computation, and we
report its outcome. We did not find these results in the literature, but we make no claim of
novelty or priority.

## Main results

- **Theorem 1.1.** $k=c(G)$ for a finite connected graph $G$ if and only if
  $k\notin\{2,4,5,8,9,16\}$.
- **Theorem 1.2.** For every attainable $k$, the least order of a connected graph with $c(G)=k$
  is $\lfloor\log_2k\rfloor+1$ if $k\ne25$, and $6$ if $k=25$.
- **Theorem 1.3.** For $m\ge6$, every integer in $[2^{m-1},2^m-1]$ is $c(G)$ for a connected graph
  with exactly $m$ vertices. For $m\ge7$, every integer in $[m,2^m-1]$ is $c(K)$ for a graph with
  exactly $m$ vertices.
- **Proposition 3.2 (the gap above the path).** A connected graph on $n\ge4$ vertices that is not a
  path has $c(G)\ge T(n)+n-3$, where $T(n)=n(n+1)/2$. Equality holds for the spider with legs
  $1,1,n-3$.
- **Proposition 7.3 (computer-assisted, via Czabarka–Székely–Wagner).** The number $F(G)$ of all
  connected subgraphs takes every positive value except
  $2,4,5,7,8,9,12,13,14,16,19,22,23,35,38,39,46$.

## Contents

| Path | Description |
|---|---|
| [`paper/connected-induced-subgraphs-inverse-problem.pdf`](paper/connected-induced-subgraphs-inverse-problem.pdf) | The paper (PDF) |
| [`paper/connected-induced-subgraphs-inverse-problem.tex`](paper/connected-induced-subgraphs-inverse-problem.tex) | LaTeX source (`amsart`, single file, figures in TikZ; compile with `pdflatex` twice) |
| [`lean/`](lean/) | Lean 4 / Mathlib formalization, library `ConnectedSets`; see [`lean/README.md`](lean/README.md) and [`lean/CHECKS.txt`](lean/CHECKS.txt) |
| [`code/f_values.py`](code/f_values.py) | The search of Proposition 7.3: every connected graph with $F\le89$, with two independent ways of computing $F$ |
| [`code/check_witnesses.py`](code/check_witnesses.py) | Decodes the graph6 strings of Appendix A from the LaTeX source and recounts $c$ |
| [`code/construct.py`](code/construct.py) | The construction of Section 4, implemented literally; writes the certificate of Lemma 4.4 and the gaps of Remark 4.5 |
| [`code/atlas_dump.py`](code/atlas_dump.py), [`code/f_edge_subsets.c`](code/f_edge_subsets.c) | Cross-check of $c$ and $F$ by vertex and edge subsets on all connected graphs with at most seven vertices |
| [`data/`](data/) | Outputs: `f_values_output.txt`, `f_graphs_le_89.csv` (the 177 graphs with $F\le89$), `check_witnesses_output.txt`, `construct_output.txt`, `base_certificate.txt` (353 derivations), `witnesses_small.csv` (witnesses with edge lists for every value up to 255) |
| [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md) | The AI disclosure, as in the paper |
| `MANIFEST.txt`, `VERSION` | SHA-256 checksums of all files; version number |
| [`LICENSE.md`](LICENSE.md), [`CITATION.cff`](CITATION.cff), `.zenodo.json` | License; citation and archiving metadata |

The census of all graphs with at most eight vertices (Table 5 of the paper), the full check of the
construction, and the re-verification of the subtree theorem of Czabarka–Székely–Wagner are in the
repository of the companion paper,
[ALL-FINITE-CARDINALITIES-OF-THE-HYPERSPACE-OF-REGULAR-SUBCONTINUA](https://github.com/LucasAlves8Sp/ALL-FINITE-CARDINALITIES-OF-THE-HYPERSPACE-OF-REGULAR-SUBCONTINUA)
(directories `code` and `data`, map in `CHECKS.md`).

## The Lean formalization

The library `ConnectedSets` (Lean `v4.35.0`, Mathlib commit
`6015dbbfc399f4548bafd46f9560ff61595fd328`, 20 modules, 4623 lines) formalizes the results of
Sections 2–6 and Lemma 7.2 of the paper. The file `lean/ConnectedSets/Paper.lean` states them with
the paper's numbering. The formalization:

- uses no `sorry`, no `native_decide` and no added axioms;
- has 31 statements in `Paper.lean`, all of which depend only on `propext`, `Classical.choice`
  and `Quot.sound`;
- was replayed through the kernel with `leanchecker` (all modules, and with `--fresh` the whole
  import closure);
- was checked by the independent type checker `nanoda` (10538 declarations, no errors).

```
cd lean
lake exe cache get          # optional: download a compiled Mathlib
lake build
lake env lean CheckAxioms.lean
```

Not formalized:
- the general formulas of Example 2.2 (the instances used in the proofs are checked by the kernel);
- the census for six to eight vertices;
- the running time in Remark 5.1;
- Remark 7.1 and Proposition 7.3, which rely on the computer-assisted theorem of
  Czabarka–Székely–Wagner;
- Appendix A.

The topological Theorem 7.4 is formalized in the companion repository.

## Reproducing the computations

```
cd code
python3 f_values.py 89 > ../data/f_values_output.txt      # also writes ../data/f_graphs_le_89.csv
python3 check_witnesses.py > ../data/check_witnesses_output.txt
cd ..
python3 code/construct.py > data/construct_output.txt      # also writes data/base_certificate.txt
python3 lean/gen/gen_base.py && python3 lean/gen/gen_intervals.py   # regenerate lean/ConnectedSets/{Sporadic,Base,Intervals}.lean
```

These commands reproduce every file in `data/` and the three generated Lean modules byte for byte.
They were tested with Python 3.13 and NetworkX 3.7. `f_values.py` and `atlas_dump.py` need
NetworkX; `check_witnesses.py`, `construct.py` and the generators use only the standard library.

## How the problem arose

The question comes from continuum theory. Ordoñez asked which finite numbers occur as the number
of regular subcontinua of a continuum (Topology Appl. 234 (2018), Problem 4.14). Camargo, Ordoñez
and Ramírez reduced the question to the values of $c(G)$ (Appl. Gen. Topol. 25 (2024)). They
excluded $2,4,5,8,9$, found by computer that $16$ is missing while $17,\dots,255$ occur, and asked
whether every $k\ge256$ occurs (Question 3.21). The companion paper answers this. This paper
presents the graph-theoretic result on its own, with complete proofs and a Lean formalization.

## AI disclosure

Artificial intelligence was used extensively in this work, both to obtain the results and to check
them.
- The main model used to solve the problem and to prove the theorems was Claude Opus 5.5
  (Anthropic).
- ChatGPT-Astra (OpenAI) was used, together with the author, to read the manuscript and check the
  arguments.
- AI was also used extensively for proofreading, proof checking, and repeated rounds of checking
  the arguments and comparing proofs.

No independent expert has yet verified the proofs. See [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md).

## How to cite

See [`CITATION.cff`](CITATION.cff).

> L. Alves de Almeida, *The inverse problem for the number of connected induced subgraphs*,
> preprint, version 1.0, 2026,
> https://github.com/LucasAlves8Sp/THE-INVERSE-PROBLEM-FOR-THE-NUMBER-OF-CONNECTED-INDUCED-SUBGRAPHS

## Status

This is a preprint that has not been peer reviewed. We searched the literature and did not find this
classification. We make no claim of novelty or priority, and references are welcome.

## License

The paper and the data are licensed under CC BY 4.0, and the programs and the Lean formalization
under the Apache License 2.0; see [`LICENSE.md`](LICENSE.md).
